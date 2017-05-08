Require Import FunctionalExtensionality.

Require Import Disk.
Require Import Automation.

Require Import Shallow.ProgLang.Prog.
Require Import Shallow.ProgLang.Hoare Shallow.ProgLang.HoareRecovery.
Require Import Shallow.TwoDiskProg.
Require Import Shallow.TwoDiskProg Shallow.TwoDiskProgTheorems.
Require Import Shallow.SeqDiskProg.

Require Import MaybeHolds.
Require Import Interpret.

Module RD.

  Definition Read (a:addr) : TD.prog block :=
    mv0 <- Prim (TD.Read d0 a);
      match mv0 with
      | Working v => Ret v
      | Failed => mv2 <- Prim (TD.Read d1 a);
                   match mv2 with
                   | Working v => Ret v
                   | Failed => Ret block0
                   end
      end.

  Definition Write (a:addr) (b:block) : TD.prog unit :=
    _ <- Prim (TD.Write d0 a b);
      _ <- Prim (TD.Write d1 a b);
      Ret tt.

  Definition DiskSize : TD.prog nat :=
    msz <- Prim (TD.DiskSize d0);
      match msz with
      | Working sz => Ret sz
      | Failed => msz <- Prim (TD.DiskSize d1);
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

  Definition fixup (a:addr) : TD.prog RecStatus :=
    mv0 <- Prim (TD.Read d0 a);
      match mv0 with
      | Working v => mv2 <- Prim (TD.Read d1 a);
                      match mv2 with
                      | Working v' => if v == v' then
                                       Ret Continue
                                     else
                                       mu <- Prim (TD.Write d1 a v);
                                       Ret (match mu with
                                            | Working _ => RepairDone
                                            | Failed => DiskFailed d1
                                            end)
                      | Failed => Ret (DiskFailed d1)
                      end
      | Failed => Ret (DiskFailed d0)
      end.

  (* recursively performs recovery at [a-1], [a-2], down to 0 *)
  Fixpoint recover_at (a:addr) : TD.prog RecStatus :=
    match a with
    | 0 => Ret RepairDone
    | S n => s <- fixup n;
              match s with
              | Continue => recover_at n
              | RepairDone => Ret RepairDone
              | DiskFailed i => Ret (DiskFailed i)
              end
    end.

  Definition Recover : TD.prog unit :=
    sz <- DiskSize;
      _ <- recover_at sz;
      Ret tt.

  Definition op_impl T (op:D.Op T) : TD.prog T :=
    match op with
    | D.Read a => Read a
    | D.Write a b => Write a b
    | D.DiskSize => DiskSize
    end.

  Definition interpret := Interpret.interpret op_impl.

  Definition abstraction (state:TD.State) : D.State :=
    match state with
    | TD.Disks (Some d) _ _ => d
    | TD.Disks None (Some d) _ => d
    | _ => empty_disk (* impossible *)
    end.

  Definition invariant (state:TD.State) :=
    match state with
    | TD.Disks (Some d_0) (Some d_1) _ =>
      d_0 = d_1
    | _ => True
    end.

  Lemma exists_tuple2 : forall A B (P: A * B -> Prop),
      (exists a b, P (a, b)) ->
      (exists p, P p).
  Proof.
    intros.
    repeat deex; eauto.
  Qed.

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
           | _ => autorewrite with upd in *
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

  Theorem Read_ok : forall a,
      prog_spec
        (fun d state =>
           {|
             pre := TD.disk0 state |= eq d /\
                    TD.disk1 state |= eq d;
             post :=
               fun r state' =>
                 d a |= eq r /\
                 TD.disk0 state' |= eq d /\
                 TD.disk1 state' |= eq d;
             crash :=
               fun state' =>
                 TD.disk0 state' |= eq d /\
                 TD.disk1 state' |= eq d;
           |})
        (Read a)
        TD.step.
  Proof.
    intros; eapply prog_ok_to_spec; simplify.
    eauto.

    unfold Read.

    step.
    descend; intuition eauto.

    destruct r; step.
    descend; intuition eauto; simplify.

    destruct r; step.
  Qed.

  Theorem Write_ok : forall a b,
      prog_spec
        (fun d state =>
           {|
             pre :=
               TD.disk0 state |= eq d /\
               TD.disk1 state |= eq d;
             post :=
               fun r state' =>
                 r = tt /\
                 TD.disk0 state' |= eq (diskUpd d a b) /\
                 TD.disk1 state' |= eq (diskUpd d a b);
             crash :=
               fun state' =>
                 (TD.disk0 state' |= eq d /\
                  TD.disk1 state' |= eq d) \/
                 (a < size d /\
                  TD.disk0 state' |= eq (diskUpd d a b) /\
                  TD.disk1 state' |= eq d) \/
                 (TD.disk0 state' |= eq (diskUpd d a b) /\
                  TD.disk1 state' |= eq (diskUpd d a b));
           |})
        (Write a b)
        TD.step.
  Proof.
    intros; eapply prog_ok_to_spec; simplify.
    intuition eauto.

    unfold Write.

    step.
    descend; intuition eauto.
    destruct r; step.
    descend; intuition eauto.

    step.
    destruct r; intuition eauto.
    destruct (lt_dec a (size a0)).
    eauto 10.
    autorewrite with upd in *.
    eauto.

    descend; intuition eauto; simplify.
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
      prog_ok
        (fun d state =>
           {|
             pre :=
               (* for simplicity we only consider in-bounds addresses, though if
                  a is out-of-bounds fixup just might uselessly write to disk and not do
                  anything *)
               a < size d /\
               TD.disk0 state |= eq d /\
               TD.disk1 state |= eq d;
             post :=
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
             crash :=
               fun state' =>
                 TD.disk0 state' |= eq d /\
                 TD.disk1 state' |= eq d;
           |})
        (fixup a)
        TD.step.
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

  Hint Rewrite diskUpd_maybe_same using (solve [ auto ]) : upd.

  Theorem fixup_correct_addr_ok : forall a,
      prog_ok
        (fun '(d, b) state =>
           {|
             pre :=
               a < size d /\
               TD.disk0 state |= eq (diskUpd d a b) /\
               TD.disk1 state |= eq d;
             post :=
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
             crash :=
               fun state' =>
                 (TD.disk0 state' |= eq (diskUpd d a b) /\
                  TD.disk1 state' |= eq d) \/
                 (TD.disk0 state' |= eq d /\
                  TD.disk1 state' |= eq d);
           |})
        (fixup a)
        TD.step.
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
    destruct r; intuition eauto; simplify; finish.
  Qed.

  Theorem fixup_wrong_addr_ok : forall a,
      prog_ok
        (fun '(d, b, a') state =>
           {|
             pre :=
               a < size d /\
               (* recovery, working from end of disk, has not yet reached the
                  correct address *)
               a' < a /\
               TD.disk0 state |= eq (diskUpd d a' b) /\
               TD.disk1 state |= eq d;
             post :=
               fun r state' =>
                 match r with
                 | Continue =>
                   TD.disk0 state' |= eq (diskUpd d a' b) /\
                   TD.disk1 state' |= eq d
                 | RepairDone =>
                   (* since the address is wrong, the only way we finish is if a
                  disk fails, which we explicitly report *)
                   False
                 | DiskFailed i =>
                   match i with
                   | d0 => TD.disk0 state' |= eq d /\
                          TD.disk1 state' |= eq d
                   | d1 => TD.disk0 state' |= eq (diskUpd d a' b) /\
                          TD.disk1 state' |= eq (diskUpd d a' b)
                   end
                 end;
             crash :=
               fun state' =>
                 (TD.disk0 state' |= eq (diskUpd d a' b) /\
                  TD.disk1 state' |= eq d) \/
                 (TD.disk0 state' |= eq d /\
                  TD.disk1 state' |= eq d);
           |})
        (fixup a)
        TD.step.
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
    destruct r; intuition eauto; simplify; finish.
    assert (a' <> a) by eauto using PeanoNat.Nat.lt_neq.
    autorewrite with upd in *.
    assert (v = v0) by eauto using disks_eq_inbounds.
    contradiction.
  Qed.

  Inductive DiskStatus :=
  | FullySynced
  | OutOfSync (a:addr) (b:block).

  Theorem fixup_ok : forall a,
      prog_ok
        (fun '(d, s) state =>
           {|
             pre :=
               a < size d /\
               match s with
               | FullySynced => TD.disk0 state |= eq d /\
                               TD.disk1 state |= eq d
               | OutOfSync a' b => a' <= a /\
                                  TD.disk0 state |= eq (diskUpd d a' b) /\
                                  TD.disk1 state |= eq d
               end;
             post :=
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
             crash :=
               fun state' =>
                 match s with
                 | FullySynced => TD.disk0 state' |= eq d /\
                                 TD.disk1 state' |= eq d
                 | OutOfSync a' b =>
                   (TD.disk0 state' |= eq (diskUpd d a' b) /\
                    TD.disk1 state' |= eq d) \/
                   (TD.disk0 state' |= eq d /\
                    TD.disk1 state' |= eq d)
                 end;
           |})
        (fixup a)
        TD.step.
  Proof.
    intro_begin; simplify.
    destruct s; intuition eauto.
    - step_prog_with ltac:(eapply fixup_equal_ok); simplify; finish.
      descend; intuition eauto.

      step.
      destruct r; intuition eauto; try congruence.
    - apply PeanoNat.Nat.lt_eq_cases in H3; intuition.
      + step_prog_with ltac:(eapply fixup_wrong_addr_ok); simplify; finish.
        descend; intuition eauto.

        step.
        destruct r; intuition eauto.
      + step_prog_with ltac:(eapply fixup_correct_addr_ok); simplify; finish.
        descend; intuition eauto.

        step.
        destruct r; intuition eauto.
  Qed.

  Hint Extern 1 {{ fixup _; _ }} => apply fixup_ok : prog.

  Hint Resolve Lt.lt_n_Sm_le.

  Theorem recover_at_ok : forall a,
      prog_ok
        (fun '(d, s) state =>
           {|
             pre :=
               a <= size d /\
               match s with
               | FullySynced => TD.disk0 state |= eq d /\
                               TD.disk1 state |= eq d
               | OutOfSync a' b => a' < a /\
                                  TD.disk0 state |= eq (diskUpd d a' b) /\
                                  TD.disk1 state |= eq d
               end;
             post :=
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
             crash :=
               fun state' =>
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
        TD.step.
  Proof.
    induction a; simpl; intros.
    - eapply ret_prog_ok; simplify; finish.
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

  Hint Extern 1 {{ recover_at _; _ }} => apply recover_at_ok : prog.

  Theorem DiskSize_ok :
    prog_ok
      (fun '(d, s) state =>
         {|
           pre :=
             match s with
             | FullySynced => TD.disk0 state |= eq d /\
                             TD.disk1 state |= eq d
             | OutOfSync a b => a < size d /\
                               TD.disk0 state |= eq (diskUpd d a b) /\
                               TD.disk1 state |= eq d
             end;
           post :=
             fun r state' =>
               r = size d /\
               match s with
               | FullySynced => TD.disk0 state' |= eq d /\
                               TD.disk1 state' |= eq d
               | OutOfSync a b => a < size d /\
                                 TD.disk0 state' |= eq (diskUpd d a b) /\
                                 TD.disk1 state' |= eq d
               end;
           crash :=
             fun state' =>
               match s with
               | FullySynced => TD.disk0 state' |= eq d /\
                               TD.disk1 state' |= eq d
               | OutOfSync a b => a < size d /\
                                 TD.disk0 state' |= eq (diskUpd d a b) /\
                                 TD.disk1 state' |= eq d
               end;
         |})
      (DiskSize)
      TD.step.
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

  Hint Extern 1 {{ DiskSize; _ }} => apply DiskSize_ok : prog.

  Theorem Recover_ok :
    prog_loopspec
      (fun '(d, s) state =>
         {|
           pre :=
             match s with
             | FullySynced => TD.disk0 state |= eq d /\
                             TD.disk1 state |= eq d
             | OutOfSync a b => a < size d /\
                               TD.disk0 state |= eq (diskUpd d a b) /\
                               TD.disk1 state |= eq d
             end;
           post :=
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
           crash :=
             fun state' =>
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
      TD.step.
  Proof.
    eapply idempotent_loopspec; simpl.
    - unfold Recover; intros.
      eapply prog_ok_to_spec; simplify.
      + destruct s; intuition eauto.
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
    - unfold idempotent; intuition; simplify.
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
        (Read a) Recover
        TD.step.
  Proof.
    intros.
    eapply prog_rspec_from_crash.
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
        (Write a b) Recover
        TD.step.
  Proof.
    intros.
    eapply prog_rspec_from_crash.
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
      (DiskSize) Recover
      TD.step.
  Proof.
    eapply prog_rspec_from_crash.
    eapply prog_ok_to_spec; [ | apply DiskSize_ok ]; simplify.
    destruct s; intuition eauto.
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

  Theorem prog_spec_exec : forall `(spec: Specification A T State) `(p: prog opT T)
                             `(step: Semantics opT State),
      prog_spec spec p step ->
      forall state r, exec step p state r ->
             forall a, pre (spec a state) ->
                  match r with
                  | Finished v state' => post (spec a state) v state'
                  | Crashed state' => crash (spec a state) state'
                  end.
  Proof.
    unfold prog_spec; intros.
    eapply H; eauto.
  Qed.

  Lemma invariant_to_disks_eq : forall state,
      invariant state ->
      TD.disk0 state |= eq (abstraction state) /\
      TD.disk1 state |= eq (abstraction state).
  Proof.
    destruct state; simpl; intros.
    destruct matches in *; eauto.
  Qed.

  Lemma disks_eq_to_invariant : forall state d,
      TD.disk0 state |= eq d ->
      TD.disk1 state |= eq d ->
      invariant state.
  Proof.
    destruct state; simpl; intros.
    destruct matches in *; eauto.
  Qed.

  Lemma disks_eq_to_abstraction : forall state d,
      TD.disk0 state |= eq d ->
      TD.disk1 state |= eq d ->
      abstraction state = d.
  Proof.
    destruct state; simpl; intros.
    destruct matches in *; eauto.
    exfalso; eauto.
  Qed.

  Hint Extern 1 (TD.disk0 _ |= eq (abstraction _)) => apply invariant_to_disks_eq.
  Hint Extern 1 (TD.disk1 _ |= eq (abstraction _)) => apply invariant_to_disks_eq.
  Hint Resolve disks_eq_to_invariant disks_eq_to_abstraction.

  Theorem RD_ok : interpretation_rexec
                    op_impl
                    Recover
                    TD.step D.step
                    invariant
                    abstraction.
  Proof.
    eapply interpret_rexec; intros; eauto.
    - destruct op; simpl in *.
      + eapply prog_rspec_weaken.
        eapply Read_rok.
        unfold rspec_impl; simplify.
        exists (abstraction state); intuition eauto.
      + eapply prog_rspec_weaken.
        eapply Write_rok.
        unfold rspec_impl; simplify.
        exists (abstraction state); intuition eauto.
      + eapply prog_rspec_weaken.
        eapply DiskSize_rok.
        unfold rspec_impl; simplify.
        exists (abstraction state); intuition eauto.
    - (* prove recovery correctly works when not doing anything (the invariant
         is already true) *)
      eapply prog_loopspec_weaken.
      eapply Recover_ok.
      unfold spec_impl; simplify.
      exists (abstraction state), FullySynced; intuition eauto.

      Grab Existential Variables.
      all: auto.
  Qed.

End RD.
