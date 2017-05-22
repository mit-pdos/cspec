Require Import Automation.
Require Import Disk.

Require Import Refinement.Interface.
Require Import Refinement.TwoDiskAPI.
Require Import Refinement.ProgLang.Prog.
Require Import Refinement.ProgLang.Hoare.

Require Import Refinement.ReplicatedDisk.Step.
Require Import Refinement.ReplicatedDisk.DiskSize.

Require Import MaybeHolds.

Section ReplicatedDiskRecovery.

    Variable (td:Interface TD.API).

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
      sz <- DiskSize td;
        _ <- recover_at sz;
        Ret tt.

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
               pre :=
                 (* for simplicity we only consider in-bounds addresses, though
                    if a is out-of-bounds fixup just might uselessly write to
                    disk and not do anything *)
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
               recover :=
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
               recover :=
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
               recover :=
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

    (* To make these specifications precise while also covering both the already
    synced and diverged disks cases, we keep track of which input state we're
    in from the input and use it to give an exact postcondition. *)
    Inductive DiskStatus :=
    | FullySynced
    | OutOfSync (a:addr) (b:block).

    Theorem fixup_ok : forall a,
        prog_rok
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
               recover :=
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

    Hint Extern 1 {{ fixup _; _ }} => apply fixup_ok : prog.

    Hint Resolve Lt.lt_n_Sm_le.

    Hint Rewrite diskUpd_size : rd.

    Theorem recover_at_ok : forall a,
        prog_rok
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
               recover :=
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

    Hint Extern 1 {{ recover_at _; _ }} => apply recover_at_ok : prog.

    Definition Recover_spec :=
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
             fun (_:unit) state' =>
               match s with
               | FullySynced => TD.disk0 state' |= eq d /\
                               TD.disk1 state' |= eq d
               | OutOfSync a b =>
                 (TD.disk0 state' |= eq d /\
                  TD.disk1 state' |= eq d) \/
                 (TD.disk0 state' |= eq (diskUpd d a b) /\
                  TD.disk1 state' |= eq (diskUpd d a b))
               end;
           recover :=
             fun (_:unit) state' =>
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
         |}).

    Theorem Recover_rok :
      prog_rspec
        Recover_spec
        (Recover)
        (irec td)
        (refinement td).
    Proof.
      unfold Recover, Recover_spec; intros.
      eapply prog_rok_to_rspec; simplify.
      - step.
        destruct s; simplify.
        + exists d, d; intuition eauto.
          step.
          exists d, FullySynced; intuition eauto.

          step.
        + exists (diskUpd d a b), d; (intuition eauto); simplify.
          step.

          exists d, (OutOfSync a b); intuition eauto.
          step.

          destruct r; intuition eauto.
          destruct i; intuition eauto.
      - destruct s; intuition eauto.
    Qed.

    Theorem Recover_ok :
      prog_loopspec
        Recover_spec
        (Recover)
        (irec td)
        (refinement td).
    Proof.
      eapply idempotent_loopspec; simpl.
      - eapply Recover_rok.
      - unfold idempotent; intuition; simplify.
        rename a0 into d.
        destruct b; intuition eauto.
        exists d, FullySynced; intuition eauto.
        exists d, FullySynced; intuition eauto.
        exists d, (OutOfSync a b); intuition eauto.
        exists (diskUpd d a b), FullySynced; intuition eauto.
    Qed.

End ReplicatedDiskRecovery.
