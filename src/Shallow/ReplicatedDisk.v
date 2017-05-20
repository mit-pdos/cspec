Require Import FunctionalExtensionality.

Require Import Disk.
Require Import Automation.

Require Import Shallow.ProgLang.Prog.
Require Import Shallow.ProgLang.Hoare Shallow.ProgLang.HoareRecovery.
Require Import Shallow.ProgLang.ProgTheorems.
Require Import Shallow.TwoDiskAPI Shallow.TwoDiskProgTheorems.
Require Import Shallow.SeqDiskAPI.

Require Import MaybeHolds.
Require Import Shallow.Interface.

Module RD.

  Section ReplicatedDisk.

    Variable (td:Interface TD.API).

    Definition Read (a:addr) : prog block :=
      mv0 <- Prim td (TD.Read d0 a);
        match mv0 with
        | Working v => Ret v
        | Failed => mv2 <- Prim td (TD.Read d1 a);
                     match mv2 with
                     | Working v => Ret v
                     | Failed => Ret block0
                     end
        end.

    Definition Write (a:addr) (b:block) : prog unit :=
      _ <- Prim td (TD.Write d0 a b);
        _ <- Prim td (TD.Write d1 a b);
        Ret tt.

    Definition DiskSize : prog nat :=
      msz <- Prim td (TD.DiskSize d0);
        match msz with
        | Working sz => Ret sz
        | Failed => msz <- Prim td (TD.DiskSize d1);
                     match msz with
                     | Working sz => Ret sz
                     | Failed => Ret 0
                     end
        end.

    (* Recovery tracks what happens at each step in order to implement control
       flow. *)
    Inductive RecStatus :=
    (* continue working, nothing interesting has happened *)
    | Continue
    (* some address has been repaired (or the recovery has exhausted the
       addresses) - only one address can be out of sync and thus only it must be
       recovered. *)
    | RepairDone
    (* one of the disks has failed, so don't bother continuing recovery since the
       invariant is now trivially satisfied *)
    | DiskFailed (i:diskId).

    Definition fixup (a:addr) : prog RecStatus :=
      mv0 <- Prim td (TD.Read d0 a);
        match mv0 with
        | Working v => mv2 <- Prim td (TD.Read d1 a);
                        match mv2 with
                        | Working v' => if v == v' then
                                         Ret Continue
                                       else
                                         mu <- Prim td (TD.Write d1 a v);
                                         Ret (match mu with
                                              | Working _ => RepairDone
                                              | Failed => DiskFailed d1
                                              end)
                        | Failed => Ret (DiskFailed d1)
                        end
        | Failed => Ret (DiskFailed d0)
        end.

    (* recursively performs recovery at [a-1], [a-2], down to 0 *)
    Fixpoint recover_at (a:addr) : prog RecStatus :=
      match a with
      | 0 => Ret RepairDone
      | S n => s <- fixup n;
                match s with
                | Continue => recover_at n
                | RepairDone => Ret RepairDone
                | DiskFailed i => Ret (DiskFailed i)
                end
      end.

    Definition Recover : prog unit :=
      sz <- DiskSize;
        _ <- recover_at sz;
        Ret tt.

    Definition op_impl T (op:D.Op T) : prog T :=
      match op with
      | D.Read a => Read a
      | D.Write a b => Write a b
      | D.DiskSize => DiskSize
      end.

    Definition rd_abstraction (state:TD.State) : D.State :=
      match state with
      | TD.Disks (Some d) _ _ => d
      | TD.Disks None (Some d) _ => d
      | _ => empty_disk (* impossible *)
      end.

    Definition rd_invariant (state:TD.State) :=
      match state with
      | TD.Disks (Some d_0) (Some d_1) _ =>
        d_0 = d_1
      | _ => True
      end.

    (* TODO: replace this with refinement composition (need to generalize
       refinement to allow two arbitrary states - current Refinement is a
       low-level WorldRefinement) *)
    Definition rd_refinement :=
      {| invariant := fun w => invariant (refinement td) w /\
                            rd_invariant (abstraction (refinement td) w);
         abstraction := fun w => rd_abstraction (abstraction (refinement td) w) |}.

    Lemma exists_tuple2 : forall A B (P: A * B -> Prop),
        (exists a b, P (a, b)) ->
        (exists p, P p).
    Proof.
      intros.
      repeat deex; eauto.
    Qed.

    (* we use a focused hint database for rewriting because autorewrite becomes
       very slow with just a handful of patterns *)
    Create HintDb rd.

    Ltac simplify :=
      repeat match goal with
             | |- forall _, _ => intros
             | _ => deex
             | _ => destruct_tuple
             | |- _ /\ _ => split; [ solve [auto] | ]
             | |- _ /\ _ => split; [ | solve [auto] ]
             (* TODO: extract the match pattern inside the exists on a0 and use
                those names in exists_tuple *)
             | |- exists (_: _*_), _ => apply exists_tuple2
             | _ => progress simpl in *
             | _ => progress safe_intuition
             | _ => progress subst
             | _ => progress autorewrite with rd in *
             | [ crashinv: _ -> Prop |- _ ] =>
               match goal with
               | [ H: forall _, _ -> crashinv _ |-
                           crashinv _ ] =>
                 eapply H
               end
             end.

    Ltac finish :=
      repeat match goal with
             | _ => solve_false
             | _ => congruence
             | _ => solve [ intuition eauto ]
             end.

    Ltac step :=
      step_prog; simplify; finish.

    Hint Resolve pred_missing.

    Lemma both_disks_not_missing : forall state,
        TD.disk0 state |= missing ->
        TD.disk1 state |= missing ->
        False.
    Proof.
      destruct state; simpl; intros.
      destruct disk0, disk1; simpl in *; eauto.
    Qed.

    Hint Resolve both_disks_not_missing : false.

    Hint Resolve irec_noop.

    Theorem Read_ok : forall a,
        prog_rspec
          (fun d state =>
             {|
               rec_pre := TD.disk0 state |= eq d /\
                          TD.disk1 state |= eq d;
               rec_post :=
                 fun r state' =>
                   d a |= eq r /\
                   TD.disk0 state' |= eq d /\
                   TD.disk1 state' |= eq d;
               recover_post :=
                 fun _ state' =>
                   TD.disk0 state' |= eq d /\
                   TD.disk1 state' |= eq d;
             |})
          (Read a)
          (irec td)
          (refinement td).
    Proof.
      intros; eapply prog_rok_to_rspec; simplify.

      unfold Read.

      step.
      descend; intuition eauto.

      destruct r; step.
      descend; (intuition eauto); simplify.

      destruct r; step.
    Qed.

    Theorem Write_ok : forall a b,
        prog_rspec
          (fun d state =>
             {|
               rec_pre :=
                 TD.disk0 state |= eq d /\
                 TD.disk1 state |= eq d;
               rec_post :=
                 fun r state' =>
                   r = tt /\
                   TD.disk0 state' |= eq (diskUpd d a b) /\
                   TD.disk1 state' |= eq (diskUpd d a b);
               recover_post :=
                 fun _ state' =>
                   (TD.disk0 state' |= eq d /\
                    TD.disk1 state' |= eq d) \/
                   (a < size d /\
                    TD.disk0 state' |= eq (diskUpd d a b) /\
                    TD.disk1 state' |= eq d) \/
                   (TD.disk0 state' |= eq (diskUpd d a b) /\
                    TD.disk1 state' |= eq (diskUpd d a b));
             |})
          (Write a b)
          (irec td)
          (refinement td).
    Proof.
      intros; eapply prog_rok_to_rspec; simplify.
      intuition eauto.

      unfold Write.

      step.
      descend; intuition eauto 10.
      destruct r; step.
      descend; intuition eauto.

      step.
      destruct r; (intuition eauto); simplify.
      destruct (lt_dec a (size a0)).
      eauto 10.
      autorewrite with upd in *; eauto.

      descend; (intuition eauto); simplify; eauto 10.
      destruct r; step.
    Qed.

    Lemma if_lt_dec : forall A n m (a a':A),
        n < m ->
        (if lt_dec n m then a else a') = a.
    Proof.
      intros.
      destruct (lt_dec n m); auto.
      contradiction.
    Qed.

    Lemma disks_eq_inbounds : forall d a v v',
        a < size d ->
        d a |= eq v ->
        d a |= eq v' ->
        v = v'.
    Proof.
      unfold disk_get; intros.
      pose proof (diskMem_domain d a).
      rewrite if_lt_dec in H2 by auto.
      repeat deex.
      rewrite H2 in H0.
      replace (d a) in *; simpl in *; subst; auto.
    Qed.

    (* we will show that fixup does nothing once the disks are the same *)
    Theorem fixup_equal_ok : forall a,
        prog_rok
          (fun d state =>
             {|
               rec_pre :=
                 (* for simplicity we only consider in-bounds addresses, though
                    if a is out-of-bounds fixup just might uselessly write to
                    disk and not do anything *)
                 a < size d /\
                 TD.disk0 state |= eq d /\
                 TD.disk1 state |= eq d;
               rec_post :=
                 fun r state' =>
                   match r with
                   | Continue =>
                     TD.disk0 state' |= eq d /\
                     TD.disk1 state' |= eq d
                   | RepairDone => False
                   | DiskFailed i =>
                     TD.disk0 state' |= eq d /\
                     TD.disk1 state' |= eq d
                   end;
               recover_post :=
                 fun _ state' =>
                   TD.disk0 state' |= eq d /\
                   TD.disk1 state' |= eq d;
             |})
          (fixup a)
          (irec td)
          (refinement td).
    Proof.
      unfold fixup.
      step.
      descend; intuition eauto.

      destruct r; step.
      descend; intuition eauto.

      destruct r; try step.
      is_eq v v0; try step.
      assert (v = v0) by eauto using disks_eq_inbounds.
      contradiction.
    Qed.

    Lemma diskUpd_maybe_same : forall (d:disk) a b,
        d a |= eq b ->
        diskUpd d a b = d.
    Proof.
      intros.
      destruct (d a) eqn:?; simpl in *; subst;
        autorewrite with upd;
        auto.
    Qed.

    Hint Rewrite diskUpd_maybe_same using (solve [ auto ]) : rd.
    Hint Rewrite diskUpd_eq using (solve [ auto ]) : rd.

    Theorem fixup_correct_addr_ok : forall a,
        prog_rok
          (fun '(d, b) state =>
             {|
               rec_pre :=
                 a < size d /\
                 TD.disk0 state |= eq (diskUpd d a b) /\
                 TD.disk1 state |= eq d;
               rec_post :=
                 fun r state' =>
                   match r with
                   | Continue =>
                     (* could happen if b already happened to be value *)
                     TD.disk0 state' |= eq (diskUpd d a b) /\
                     TD.disk1 state' |= eq (diskUpd d a b)
                   | RepairDone =>
                     TD.disk0 state' |= eq (diskUpd d a b) /\
                     TD.disk1 state' |= eq (diskUpd d a b)
                   | DiskFailed i =>
                     match i with
                     | d0 => TD.disk0 state' |= eq d /\
                            TD.disk1 state' |= eq d
                     | d1 => TD.disk0 state' |= eq (diskUpd d a b) /\
                            TD.disk1 state' |= eq (diskUpd d a b)
                     end
                   end;
               recover_post :=
                 fun _ state' =>
                   (TD.disk0 state' |= eq (diskUpd d a b) /\
                    TD.disk1 state' |= eq (diskUpd d a b)) \/
                   (TD.disk0 state' |= eq (diskUpd d a b) /\
                    TD.disk1 state' |= eq d) \/
                   (TD.disk0 state' |= eq d /\
                    TD.disk1 state' |= eq d);
             |})
          (fixup a)
          (irec td)
          (refinement td).
    Proof.
      unfold fixup; intros.
      step.
      descend; intuition eauto.

      destruct r; try step.
      descend; intuition eauto.

      destruct r; try step.
      is_eq b v; try step.
      descend; intuition eauto.

      step.
      destruct r; (intuition eauto); simplify; finish.
    Qed.

    Theorem fixup_wrong_addr_ok : forall a,
        prog_rok
          (fun '(d, b, a') state =>
             {|
               rec_pre :=
                 a < size d /\
                 (* recovery, working from end of disk, has not yet reached the
                    correct address *)
                 a' < a /\
                 TD.disk0 state |= eq (diskUpd d a' b) /\
                 TD.disk1 state |= eq d;
               rec_post :=
                 fun r state' =>
                   match r with
                   | Continue =>
                     TD.disk0 state' |= eq (diskUpd d a' b) /\
                     TD.disk1 state' |= eq d
                   | RepairDone =>
                     (* since the address is wrong, the only way we finish is if
                        a disk fails, which we explicitly report *)
                     False
                   | DiskFailed i =>
                     match i with
                     | d0 => TD.disk0 state' |= eq d /\
                            TD.disk1 state' |= eq d
                     | d1 => TD.disk0 state' |= eq (diskUpd d a' b) /\
                            TD.disk1 state' |= eq (diskUpd d a' b)
                     end
                   end;
               recover_post :=
                 fun _ state' =>
                   (TD.disk0 state' |= eq (diskUpd d a' b) /\
                    TD.disk1 state' |= eq d) \/
                   (TD.disk0 state' |= eq d /\
                    TD.disk1 state' |= eq d);
             |})
          (fixup a)
          (irec td)
          (refinement td).
    Proof.
      unfold fixup; intros.
      step.
      descend; intuition eauto.

      destruct r; try step.
      descend; intuition eauto.

      destruct r; try step.
      is_eq v v0; try step.
      descend; intuition eauto.

      step.
      destruct r; (intuition eauto); simplify; finish.
      assert (a' <> a) by eauto using PeanoNat.Nat.lt_neq.
      autorewrite with upd in *.
      assert (v = v0) by eauto using disks_eq_inbounds.
      contradiction.

      assert (a' <> a) by eauto using PeanoNat.Nat.lt_neq.
      autorewrite with upd in *.
      assert (v = v0) by eauto using disks_eq_inbounds.
      contradiction.
    Qed.

    Inductive DiskStatus :=
    | FullySynced
    | OutOfSync (a:addr) (b:block).

    Theorem fixup_ok : forall a,
        prog_rok
          (fun '(d, s) state =>
             {|
               rec_pre :=
                 a < size d /\
                 match s with
                 | FullySynced => TD.disk0 state |= eq d /\
                                 TD.disk1 state |= eq d
                 | OutOfSync a' b => a' <= a /\
                                    TD.disk0 state |= eq (diskUpd d a' b) /\
                                    TD.disk1 state |= eq d
                 end;
               rec_post :=
                 fun r state' =>
                   match s with
                   | FullySynced => TD.disk0 state' |= eq d /\
                                   TD.disk1 state' |= eq d /\
                                   (* not actually useful *)
                                   r <> RepairDone
                   | OutOfSync a' b =>
                     match r with
                     | Continue =>
                       (a' < a /\
                        TD.disk0 state' |= eq (diskUpd d a' b) /\
                        TD.disk1 state' |= eq d) \/
                       (TD.disk0 state' |= eq (diskUpd d a' b) /\
                        TD.disk1 state' |= eq (diskUpd d a' b))
                     | RepairDone =>
                       (TD.disk0 state' |= eq d /\
                        TD.disk1 state' |= eq d) \/
                       (a = a' /\ (* not necessary, but nice to document *)
                        TD.disk0 state' |= eq (diskUpd d a' b) /\
                        TD.disk1 state' |= eq (diskUpd d a' b))
                     | DiskFailed i =>
                       match i with
                       | d0 => TD.disk0 state' |= eq d /\
                              TD.disk1 state' |= eq d
                       | d1 => TD.disk0 state' |= eq (diskUpd d a' b) /\
                              TD.disk1 state' |= eq (diskUpd d a' b)
                       end
                     end
                   end;
               recover_post :=
                 fun _ state' =>
                   match s with
                   | FullySynced => TD.disk0 state' |= eq d /\
                                   TD.disk1 state' |= eq d
                   | OutOfSync a' b =>
                     (TD.disk0 state' |= eq (diskUpd d a' b) /\
                      TD.disk1 state' |= eq (diskUpd d a' b)) \/
                     (TD.disk0 state' |= eq (diskUpd d a' b) /\
                      TD.disk1 state' |= eq d) \/
                     (TD.disk0 state' |= eq d /\
                      TD.disk1 state' |= eq d)
                   end;
             |})
          (fixup a)
          (irec td)
          (refinement td).
    Proof.
      unfold prog_rok; intros.
      eapply rdouble_cases; simplify.
      destruct s; intuition eauto.
      - rdouble_case fixup_equal_ok; simplify; finish.
        descend; intuition eauto.

        step.
        destruct r; (intuition eauto); try congruence.
      - apply PeanoNat.Nat.lt_eq_cases in H3; intuition.
        + rdouble_case fixup_wrong_addr_ok;
            simplify; finish.
          descend; intuition eauto.

          step.
          destruct r; intuition eauto.
        + rdouble_case fixup_correct_addr_ok;
            simplify; finish.
          descend; intuition eauto.

          step.
          destruct r; intuition eauto.
    Qed.

    Hint Extern 1 {{{ fixup _; _ }}} => apply fixup_ok : prog.

    Hint Resolve Lt.lt_n_Sm_le.

    Hint Rewrite diskUpd_size : rd.

    Theorem recover_at_ok : forall a,
        prog_rok
          (fun '(d, s) state =>
             {|
               rec_pre :=
                 a <= size d /\
                 match s with
                 | FullySynced => TD.disk0 state |= eq d /\
                                 TD.disk1 state |= eq d
                 | OutOfSync a' b => a' < a /\
                                    TD.disk0 state |= eq (diskUpd d a' b) /\
                                    TD.disk1 state |= eq d
                 end;
               rec_post :=
                 fun r state' =>
                   match s with
                   | FullySynced => TD.disk0 state' |= eq d /\
                                   TD.disk1 state' |= eq d /\
                                   r <> Continue
                   | OutOfSync a' b =>
                     match r with
                     | Continue => False
                     | RepairDone =>
                       (TD.disk0 state' |= eq d /\
                        TD.disk1 state' |= eq d) \/
                       (TD.disk0 state' |= eq (diskUpd d a' b) /\
                        TD.disk1 state' |= eq (diskUpd d a' b))
                     | DiskFailed i =>
                       match i with
                       | d0 => (TD.disk0 state' |= eq d /\
                               TD.disk1 state' |= eq d) \/
                              (TD.disk0 state' |= eq (diskUpd d a' b) /\
                               TD.disk1 state' |= eq (diskUpd d a' b))
                       | d1 => TD.disk0 state' |= eq (diskUpd d a' b) /\
                              TD.disk1 state' |= eq (diskUpd d a' b)
                       end
                     end
                   end;
               recover_post :=
                 fun _ state' =>
                   match s with
                   | FullySynced => TD.disk0 state' |= eq d /\
                                   TD.disk1 state' |= eq d
                   | OutOfSync a' b =>
                     (TD.disk0 state' |= eq d /\
                      TD.disk1 state' |= eq d) \/
                     (TD.disk0 state' |= eq (diskUpd d a' b) /\
                      TD.disk1 state' |= eq d) \/
                     (TD.disk0 state' |= eq (diskUpd d a' b) /\
                      TD.disk1 state' |= eq (diskUpd d a' b))
                   end;
             |})
          (recover_at a)
          (irec td)
          (refinement td).
    Proof.
      induction a; simpl; intros.
      - eapply ret_prog_rok; simplify; finish.
        destruct s; intuition eauto.
        congruence.
        inversion H1.
      - step.
        destruct s; intuition.
        exists d, FullySynced; intuition eauto.
        destruct r; step.

        exists d, FullySynced; intuition eauto.
        exists d, (OutOfSync a0 b); intuition eauto.

        destruct r; step.
        intuition.
        exists d, (OutOfSync a0 b); intuition eauto.
        exists (diskUpd d a0 b), FullySynced; intuition eauto.
        simplify; finish.
        step.
        destruct r; intuition eauto.
        destruct i; intuition eauto.
        destruct i; intuition eauto.
    Qed.

    Hint Extern 1 {{{ recover_at _; _ }}} => apply recover_at_ok : prog.

    Theorem DiskSize_ok :
      prog_rok
        (fun '(d, s) state =>
           {|
             rec_pre :=
               match s with
               | FullySynced => TD.disk0 state |= eq d /\
                               TD.disk1 state |= eq d
               | OutOfSync a b => a < size d /\
                                 TD.disk0 state |= eq (diskUpd d a b) /\
                                 TD.disk1 state |= eq d
               end;
             rec_post :=
               fun r state' =>
                 r = size d /\
                 match s with
                 | FullySynced => TD.disk0 state' |= eq d /\
                                 TD.disk1 state' |= eq d
                 | OutOfSync a b => a < size d /\
                                   TD.disk0 state' |= eq (diskUpd d a b) /\
                                   TD.disk1 state' |= eq d
                 end;
             recover_post :=
               fun _ state' =>
                 match s with
                 | FullySynced => TD.disk0 state' |= eq d /\
                                 TD.disk1 state' |= eq d
                 | OutOfSync a b => a < size d /\
                                   TD.disk0 state' |= eq (diskUpd d a b) /\
                                   TD.disk1 state' |= eq d
                 end;
           |})
        (DiskSize)
        (irec td)
        (refinement td).
    Proof.
      unfold DiskSize.

      step.
      destruct s; descend; intuition eauto.
      - destruct r; step.
        descend; intuition eauto.

        destruct r; step.
      - destruct r; step.
        descend; intuition eauto.

        destruct r; step.
    Qed.

    Hint Extern 1 {{{ DiskSize; _ }}} => apply DiskSize_ok : prog.

    Theorem Recover_ok :
      prog_rec_loopspec
        (fun '(d, s) state =>
           {|
             rec_pre :=
               match s with
               | FullySynced => TD.disk0 state |= eq d /\
                               TD.disk1 state |= eq d
               | OutOfSync a b => a < size d /\
                                 TD.disk0 state |= eq (diskUpd d a b) /\
                                 TD.disk1 state |= eq d
               end;
             rec_post :=
               fun _ state' =>
                 match s with
                 | FullySynced => TD.disk0 state' |= eq d /\
                                 TD.disk1 state' |= eq d
                 | OutOfSync a b =>
                   (TD.disk0 state' |= eq d /\
                    TD.disk1 state' |= eq d) \/
                   (TD.disk0 state' |= eq (diskUpd d a b) /\
                    TD.disk1 state' |= eq (diskUpd d a b))
                 end;
             recover_post :=
               fun _ state' =>
                 match s with
                 | FullySynced => TD.disk0 state' |= eq d /\
                                 TD.disk1 state' |= eq d
                 | OutOfSync a b =>
                   (TD.disk0 state' |= eq d /\
                    TD.disk1 state' |= eq d) \/
                   (TD.disk0 state' |= eq (diskUpd d a b) /\
                    TD.disk1 state' |= eq d) \/
                   (TD.disk0 state' |= eq (diskUpd d a b) /\
                    TD.disk1 state' |= eq (diskUpd d a b))
                 end;
           |})
        (Recover)
        (irec td)
        (refinement td).
    Proof.
      eapply rec_idempotent_loopspec; simpl.
      - unfold Recover; intros.
        eapply prog_rok_to_rspec; simplify.
        + step.
          descend; intuition eauto.

          step.
          destruct s; intuition.
          exists d, FullySynced; intuition eauto.
          step.

          exists d, (OutOfSync a b); intuition eauto.
          step.

          destruct r; intuition eauto.
          destruct i; intuition eauto.
          destruct s; simplify; eauto.
        + destruct s; intuition eauto.
      - unfold rec_idempotent; intuition; simplify.
        rename a0 into d.
        destruct b; intuition eauto.
        exists d, FullySynced; intuition eauto.
        exists d, FullySynced; intuition eauto.
        exists d, (OutOfSync a b); intuition eauto.
        exists (diskUpd d a b), FullySynced; intuition eauto.
    Qed.

    Theorem Read_rok : forall a,
        prog_rspec
          (fun d state =>
             {|
               rec_pre := TD.disk0 state |= eq d /\
                          TD.disk1 state |= eq d;
               rec_post :=
                 fun r state' =>
                   d a |= eq r /\
                   TD.disk0 state' |= eq d /\
                   TD.disk1 state' |= eq d;
               recover_post :=
                 fun _ state' =>
                   TD.disk0 state' |= eq d /\
                   TD.disk1 state' |= eq d;
             |})
          (Read a) (_ <- irec td; Recover)
          (refinement td).
    Proof.
      intros.
      eapply compose_recovery.
      eapply Read_ok.
      eapply Recover_ok.
      simplify.
      rename a0 into d.
      descend; intuition eauto.
      simplify.
      exists d, FullySynced; intuition eauto.
    Qed.

    Theorem Write_rok : forall a b,
        prog_rspec
          (fun d state =>
             {|
               rec_pre :=
                 TD.disk0 state |= eq d /\
                 TD.disk1 state |= eq d;
               rec_post :=
                 fun r state' =>
                   r = tt /\
                   TD.disk0 state' |= eq (diskUpd d a b) /\
                   TD.disk1 state' |= eq (diskUpd d a b);
               recover_post :=
                 fun _ state' =>
                   (TD.disk0 state' |= eq d /\
                    TD.disk1 state' |= eq d) \/
                   (TD.disk0 state' |= eq (diskUpd d a b) /\
                    TD.disk1 state' |= eq (diskUpd d a b));
             |})
          (Write a b) (_ <- irec td; Recover)
          (refinement td).
    Proof.
      intros.
      eapply compose_recovery.
      eapply Write_ok.
      eapply Recover_ok.
      simplify.
      rename a0 into d.
      descend; (intuition eauto); simplify.
      exists d, FullySynced; intuition eauto.
      exists d, (OutOfSync a b); intuition eauto.
      exists (diskUpd d a b), FullySynced; intuition eauto.
    Qed.

    Theorem DiskSize_rok :
      prog_rspec
        (fun d state =>
           {|
             rec_pre := TD.disk0 state |= eq d /\
                        TD.disk1 state |= eq d;
             rec_post :=
               fun r state' =>
                 r = size d /\
                 TD.disk0 state' |= eq d /\
                 TD.disk1 state' |= eq d;
             recover_post :=
               fun _ state' =>
                 TD.disk0 state' |= eq d /\
                 TD.disk1 state' |= eq d;
           |})
        (DiskSize) (_ <- irec td; Recover)
        (refinement td).
    Proof.
      eapply compose_recovery.
      eapply prog_rok_to_rspec; [ eapply DiskSize_ok | eauto | simplify ].
      eapply Recover_ok.
      simplify.

      rename a into d.
      exists d, FullySynced; intuition eauto.
      simplify.
      exists d, FullySynced; intuition eauto.
    Qed.

    Lemma read_step : forall a (state state':D.State) b,
        state a |= eq b ->
        state' = state ->
        D.step (D.Read a) state b state'.
    Proof.
      intros; subst.
      constructor; auto.
      intros.
      replace (state a) in *; auto.
    Qed.

    Lemma write_step : forall a b (state state':D.State) u,
        state' = diskUpd state a b ->
        D.step (D.Write a b) state u state'.
    Proof.
      intros; subst.
      destruct u.
      econstructor; eauto.
    Qed.

    Lemma disk_size_step : forall (state state':D.State) r,
        r = size state ->
        state' = state ->
        D.step (D.DiskSize) state r state'.
    Proof.
      intros; subst.
      econstructor; eauto.
    Qed.

    Hint Resolve read_step write_step disk_size_step.
    Hint Resolve tt.

    Lemma invariant_to_disks_eq : forall state,
        rd_invariant state ->
        TD.disk0 state |= eq (rd_abstraction state) /\
        TD.disk1 state |= eq (rd_abstraction state).
    Proof.
      destruct state; simpl; intros.
      destruct matches in *; eauto.
    Qed.

    Lemma disks_eq_to_invariant : forall state d,
        TD.disk0 state |= eq d ->
        TD.disk1 state |= eq d ->
        rd_invariant state.
    Proof.
      destruct state; simpl; intros.
      destruct matches in *; eauto.
    Qed.

    Lemma disks_eq_to_abstraction : forall state d,
        TD.disk0 state |= eq d ->
        TD.disk1 state |= eq d ->
        rd_abstraction state = d.
    Proof.
      destruct state; simpl; intros.
      destruct matches in *; eauto.
      exfalso; eauto.
    Qed.

    Hint Extern 1 (TD.disk0 _ |= eq (rd_abstraction _)) => apply invariant_to_disks_eq.
    Hint Extern 1 (TD.disk1 _ |= eq (rd_abstraction _)) => apply invariant_to_disks_eq.
    Hint Resolve disks_eq_to_invariant disks_eq_to_abstraction.

  End ReplicatedDisk.

End RD.
