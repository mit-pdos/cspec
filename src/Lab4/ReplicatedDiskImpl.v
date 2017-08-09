Require Import POCS.

Require Import TwoDiskAPI.
Require Import Common.OneDiskAPI.


Module ReplicatedDisk (td : TwoDiskAPI) <: OneDiskAPI.

  Definition read (a:addr) : proc block :=
    mv0 <- td.read d0 a;
    match mv0 with
    | Working v => Ret v
    | Failed =>
      mv2 <- td.read d1 a;
      match mv2 with
      | Working v => Ret v
      | Failed => Ret block0
      end
    end.

  Definition write (a:addr) (b:block) : proc unit :=
    _ <- td.write d0 a b;
    _ <- td.write d1 a b;
    Ret tt.

  Definition size : proc nat :=
    msz <- td.size d0;
    match msz with
    | Working sz => Ret sz
    | Failed =>
      msz <- td.size d1;
      match msz with
      | Working sz => Ret sz
      | Failed => Ret 0
      end
    end.

  Definition sizeInit : proc (option nat) :=
    sz1 <- td.size d0;
    sz2 <- td.size d1;
    match sz1 with
    | Working sz1 =>
      match sz2 with
      | Working sz2 =>
        if sz1 == sz2 then Ret (Some sz1) else Ret None
      | Failed => Ret (Some sz1)
      end
    | Failed =>
      match sz2 with
      | Working sz2 => Ret (Some sz2)
      | Failed => Ret None
      end
    end.

  (* Recursively initialize block a and below *)
  Fixpoint init_at (a:nat) : proc unit :=
    match a with
    | 0 => Ret tt
    | S a =>
      _ <- td.write d0 a block0;
      _ <- td.write d1 a block0;
      init_at a
    end.

  (* Initialize every disk block *)
  Definition init' : proc InitResult :=
    size <- sizeInit;
    match size with
    | Some sz =>
      _ <- init_at sz;
      Ret Initialized
    | None =>
      Ret InitFailed
    end.

  Definition init := then_init td.init init'.


  (**
   * Helper lemmas and tactics for proofs.
   *)

  (* As the final step in giving the correctness of the replicated disk
  operations, we prove recovery specs that include the replicated disk Recover
  function. *)

  Theorem exists_tuple2 : forall `(P: A * B -> Prop),
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
           | _ => progress autounfold in *
           | _ => progress autorewrite with rd in *
           | [ u: unit |- _ ] => destruct u
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
           | _ => solve [ intuition (subst; eauto; try congruence) ]
           | _ =>
             (* if we can solve all the side conditions automatically, then it's
             safe to run descend *)
             descend; intuition eauto;
             lazymatch goal with
             | |- proc_spec _ _ _ _ => idtac
             | _ => fail
             end
           end.

  Ltac step :=
    step_prog; simplify; finish.

  Ltac start := intros;
                match goal with
                | |- proc_spec _ _ (_ <- _; _) _ =>
                  eapply compose_recovery; eauto; simplify
                end.


  (**
   * Specifications and proofs about our implementation of the replicated disk API,
   * without considering our recovery.
   *)

  Theorem both_disks_not_missing : forall (state: TwoDiskBaseAPI.State),
      disk0 state ?|= missing ->
      disk1 state ?|= missing ->
      False.
  Proof.
    destruct state; simpl; intros.
    destruct disk0, disk1; simpl in *; eauto.
  Qed.
  Hint Resolve both_disks_not_missing : false.

  Theorem missing0_implies_any : forall (state: TwoDiskBaseAPI.State) P,
      disk0 state ?|= missing ->
      disk0 state ?|= P.
  Proof.
    destruct state; unfold missing; simpl; intros.
    destruct disk0; eauto.
    intuition.
  Qed.

  Theorem missing1_implies_any : forall (state: TwoDiskBaseAPI.State) P,
      disk1 state ?|= missing ->
      disk1 state ?|= P.
  Proof.
    destruct state; unfold missing; simpl; intros.
    destruct disk1; eauto.
    intuition.
  Qed.

  Hint Resolve missing0_implies_any.
  Hint Resolve missing1_implies_any.

  Theorem read_int_ok : forall a,
      proc_spec
        (fun d state =>
           {|
             pre := disk0 state ?|= eq d /\
                    disk1 state ?|= eq d;
             post :=
               fun r state' =>
                 diskGet d a ?|= eq r /\
                 disk0 state' ?|= eq d /\
                 disk1 state' ?|= eq d;
             recovered :=
               fun _ state' =>
                 disk0 state' ?|= eq d /\
                 disk1 state' ?|= eq d;
           |})
        (read a)
        td.recover
        td.abstr.
  Proof.
    unfold read.

    step.

    destruct r; step.
    destruct r; step.
    simplify.
  Qed.

  Hint Resolve read_int_ok.


  Theorem write_int_ok : forall a b,
      proc_spec
        (fun d state =>
           {|
             pre :=
               disk0 state ?|= eq d /\
               disk1 state ?|= eq d;
             post :=
               fun r state' =>
                 r = tt /\
                 disk0 state' ?|= eq (diskUpd d a b) /\
                 disk1 state' ?|= eq (diskUpd d a b);
             recovered :=
               fun _ state' =>
                 (disk0 state' ?|= eq d /\
                  disk1 state' ?|= eq d) \/
                 (a < diskSize d /\
                  disk0 state' ?|= eq (diskUpd d a b) /\
                  disk1 state' ?|= eq d) \/
                 (disk0 state' ?|= eq (diskUpd d a b) /\
                  disk1 state' ?|= eq (diskUpd d a b));
           |})
        (write a b)
        td.recover
        td.abstr.
  Proof.
    unfold write.

    step.

    destruct r; step.
    descend; intuition eauto.

    step.
    destruct r; (intuition eauto); simplify.
    destruct (lt_dec a (diskSize a')).
    eauto 10.
    autorewrite with upd in *; eauto.

    destruct r; step.
    simplify.
  Qed.

  Hint Resolve write_int_ok.


  Theorem size_int_ok :
    proc_spec
      (fun '(d_0, d_1) state =>
         {|
           pre :=
             disk0 state ?|= eq d_0 /\
             disk1 state ?|= eq d_1 /\
             diskSize d_0 = diskSize d_1;
           post :=
             fun r state' =>
               r = diskSize d_0 /\
               r = diskSize d_1 /\
               disk0 state' ?|= eq d_0 /\
               disk1 state' ?|= eq d_1;
           recovered :=
             fun _ state' =>
               disk0 state' ?|= eq d_0 /\
               disk1 state' ?|= eq d_1;
         |})
      (size)
      td.recover
      td.abstr.
  Proof.
    unfold size.

    step.

    destruct r; step.
    destruct r; step.
    simplify.
  Qed.

  Hint Resolve size_int_ok.


  Definition equal_after a (d_0 d_1: disk) :=
    diskSize d_0 = diskSize d_1 /\
    forall a', a <= a' -> diskGet d_0 a' = diskGet d_1 a'.

  Theorem le_eq_or_S_le : forall n m,
      n <= m ->
      n = m \/
      S n <= m /\ n <> m.
  Proof.
    intros.
    omega.
  Qed.

  Theorem equal_after_diskUpd : forall a d_0 d_1 b,
      equal_after (S a) d_0 d_1 ->
      equal_after a (diskUpd d_0 a b) (diskUpd d_1 a b).
  Proof.
    unfold equal_after; intuition.
    autorewrite with upd; eauto.
    apply le_eq_or_S_le in H; intuition subst.
    destruct (lt_dec a' (diskSize d_0)); autorewrite with upd.
    assert (a' < diskSize d_1) by congruence; autorewrite with upd; auto.
    assert (~a' < diskSize d_1) by congruence; autorewrite with upd; auto.
    autorewrite with upd; eauto.
  Qed.
  Hint Resolve equal_after_diskUpd.

  Theorem init_at_ok : forall a,
      proc_spec
        (fun '(d_0, d_1) state =>
           {| pre :=
                disk0 state ?|= eq d_0 /\
                disk1 state ?|= eq d_1 /\
                equal_after a d_0 d_1;
              post :=
                fun _ state' =>
                  exists d_0' d_1': disk,
                    disk0 state' ?|= eq d_0' /\
                    disk1 state' ?|= eq d_1' /\
                    equal_after 0 d_0' d_1';
              recovered :=
                fun _ state' => True;
           |})
        (init_at a)
        td.recover
        td.abstr.
  Proof.
    induction a; simpl; intros.
    - step.
    - step.

      step.
      destruct r; finish.
      + step.
        destruct r; simplify; finish.
      + step.
        destruct r; finish.

        Grab Existential Variables.
        exact block0.
  Qed.

  Hint Resolve init_at_ok.


  Theorem sizeInit_ok :
      proc_spec
        (fun '(d_0, d_1) state =>
           {| pre :=
                disk0 state ?|= eq d_0 /\
                disk1 state ?|= eq d_1;
              post :=
                 fun r state' =>
                  exists d_0' d_1',
                    disk0 state' ?|= eq d_0' /\
                    disk1 state' ?|= eq d_1' /\
                    match r with
                    | Some sz => diskSize d_0' = sz /\ diskSize d_1' = sz
                    | None => True
                    end;
              recovered :=
                fun _ state' => True;
           |})
        (sizeInit)
        td.recover
        td.abstr.
  Proof.
    unfold sizeInit.
    step.
    destruct r.
    step.
    - destruct r.
      + destruct (diskSize d_0 == v).
        * step.
        * step.
      + step.
    - step.
      destruct r.
      + step.
      + step.
  Qed.

  Hint Resolve sizeInit_ok.


  Theorem equal_after_0_to_eq : forall d_0 d_1,
      equal_after 0 d_0 d_1 ->
      d_0 = d_1.
  Proof.
    unfold equal_after; intuition.
    eapply disk_ext_eq; intros.
    eapply H1; omega.
  Qed.

  Theorem equal_after_size : forall d_0 d_1,
      diskSize d_0 = diskSize d_1 ->
      equal_after (diskSize d_0) d_0 d_1.
  Proof.
    unfold equal_after; intuition.
    assert (~a' < diskSize d_0) by omega.
    assert (~a' < diskSize d_1) by congruence.
    autorewrite with upd; eauto.
  Qed.

  Hint Resolve equal_after_size.
  Hint Resolve equal_after_0_to_eq.

  Theorem init'_ok :
      proc_spec
        (fun '(d_0, d_1) state =>
           {| pre :=
                disk0 state ?|= eq d_0 /\
                disk1 state ?|= eq d_1;
              post :=
                fun r state' =>
                  match r with
                  | Initialized =>
                    exists d_0' d_1',
                    disk0 state' ?|= eq d_0' /\
                    disk1 state' ?|= eq d_1' /\
                    d_0' = d_1'
                  | InitFailed =>
                    True
                  end;
              recovered :=
                fun _ state' => True;
           |})
        (init')
        td.recover
        td.abstr.
  Proof.
    unfold init.
    step.
    descend; intuition eauto.
    destruct r; step.
    step.
  Qed.

  Hint Resolve init'_ok.


  (**
   * Recovery implementation.
   *)

  Inductive RecStatus :=
  (* continue working, nothing interesting has happened *)
  | Continue
  (* some address has been repaired (or the recovery has exhausted the
     addresses) - only one address can be out of sync and thus only it must be
     recovered. *)
  (* OR, one of the disks has failed, so don't bother continuing recovery since
     the invariant is now trivially satisfied *)
  | RepairDoneOrFailed.

  Definition fixup (a:addr) : proc RecStatus :=
    mv0 <- td.read d0 a;
    match mv0 with
    | Working v =>
      mv2 <- td.read d1 a;
      match mv2 with
      | Working v' =>
        if v == v' then
          Ret Continue
        else
          mu <- td.write d1 a v;
          Ret RepairDoneOrFailed
      | Failed => Ret RepairDoneOrFailed
      end
    | Failed => Ret RepairDoneOrFailed
    end.

  (* recursively performs recovery at [a-1], [a-2], down to 0 *)
  Fixpoint recover_at (a:addr) : proc unit :=
    match a with
    | 0 => Ret tt
    | S n =>
      s <- fixup n;
      match s with
      | Continue => recover_at n
      | RepairDoneOrFailed => Ret tt
      end
    end.

  Definition Recover : proc unit :=
    sz <- size;
    _ <- recover_at sz;
    Ret tt.


  (**
   * Theorems and recovery proofs.
   *)

  Theorem if_lt_dec : forall A n m (a a':A),
      n < m ->
      (if lt_dec n m then a else a') = a.
  Proof.
    intros.
    destruct (lt_dec n m); auto.
    contradiction.
  Qed.

  Theorem disks_eq_inbounds : forall (d: disk) a v v',
      a < diskSize d ->
      diskGet d a ?|= eq v ->
      diskGet d a ?|= eq v' ->
      v = v'.
  Proof.
    intros.
    case_eq (diskGet d a); intros.
    - rewrite H2 in *. simpl in *. congruence.
    - exfalso.
      eapply disk_inbounds_not_none; eauto.
  Qed.

  (* we will show that fixup does nothing once the disks are the same *)
  Theorem fixup_equal_ok : forall a,
      proc_spec
        (fun d state =>
           {|
             pre :=
               (* for simplicity we only consider in-bounds addresses, though
                  if a is out-of-bounds fixup just might uselessly write to
                  disk and not do anything *)
               a < diskSize d /\
               disk0 state ?|= eq d /\
               disk1 state ?|= eq d;
             post :=
               fun r state' =>
                 match r with
                 | Continue =>
                   disk0 state' ?|= eq d /\
                   disk1 state' ?|= eq d
                 | RepairDoneOrFailed =>
                   disk0 state' ?|= eq d /\
                   disk1 state' ?|= eq d
                 end;
             recovered :=
               fun _ state' =>
                 disk0 state' ?|= eq d /\
                 disk1 state' ?|= eq d;
           |})
        (fixup a)
        td.recover
        td.abstr.
  Proof.
    unfold fixup.
    step.

    destruct r; step.

    destruct r; try step.
    destruct (v == v0); subst; try step.
    simplify.
    assert (v = v0) by eauto using disks_eq_inbounds.
    contradiction.
    simplify.
    simplify.
  Qed.

  Theorem diskUpd_maybe_same : forall (d:disk) a b,
      diskGet d a ?|= eq b ->
      diskUpd d a b = d.
  Proof.
    intros.
    destruct (diskGet d a) eqn:?; simpl in *; subst;
      autorewrite with upd;
      auto.
  Qed.

  Hint Rewrite diskUpd_maybe_same using (solve [ auto ]) : rd.
  Hint Rewrite diskUpd_eq using (solve [ auto ]) : rd.

  Theorem fixup_correct_addr_ok : forall a,
      proc_spec
        (fun '(d, b) state =>
           {|
             pre :=
               a < diskSize d /\
               disk0 state ?|= eq (diskUpd d a b) /\
               disk1 state ?|= eq d;
             post :=
               fun r state' =>
                 match r with
                 | Continue =>
                   (* could happen if b already happened to be value *)
                   disk0 state' ?|= eq (diskUpd d a b) /\
                   disk1 state' ?|= eq (diskUpd d a b)
                 | RepairDoneOrFailed =>
                   disk0 state' ?|= eq (diskUpd d a b) /\
                   disk1 state' ?|= eq (diskUpd d a b) \/
                   disk0 state' ?|= eq d /\
                   disk1 state' ?|= eq d
                 end;
             recovered :=
               fun _ state' =>
                 (disk0 state' ?|= eq (diskUpd d a b) /\
                  disk1 state' ?|= eq (diskUpd d a b)) \/
                 (disk0 state' ?|= eq (diskUpd d a b) /\
                  disk1 state' ?|= eq d) \/
                 (disk0 state' ?|= eq d /\
                  disk1 state' ?|= eq d);
           |})
        (fixup a)
        td.recover
        td.abstr.
  Proof.
    unfold fixup; intros.
    step.

    destruct r; try step.

    destruct r; try step.
    match goal with
    | |- context[diskUpd _ _ ?b] =>
      destruct (b == v); subst; try step
    end.

    simplify.

    step.
    destruct r; (intuition eauto); simplify; finish.

    simplify.
    simplify.
  Qed.

  Hint Resolve PeanoNat.Nat.lt_neq.
  Hint Rewrite diskUpd_neq : rd.
  Hint Resolve disks_eq_inbounds.

  Theorem fixup_wrong_addr_ok : forall a,
      proc_spec
        (fun '(d, b, a') state =>
           {|
             pre :=
               a < diskSize d /\
               (* recovery, working from end of disk, has not yet reached the
                  correct address *)
               a' < a /\
               disk0 state ?|= eq (diskUpd d a' b) /\
               disk1 state ?|= eq d;
             post :=
               fun r state' =>
                 match r with
                 | Continue =>
                   disk0 state' ?|= eq (diskUpd d a' b) /\
                   disk1 state' ?|= eq d
                 | RepairDoneOrFailed =>
                   disk0 state' ?|= eq d /\
                   disk1 state' ?|= eq d \/
                   disk0 state' ?|= eq (diskUpd d a' b) /\
                   disk1 state' ?|= eq (diskUpd d a' b)
                 end;
             recovered :=
               fun _ state' =>
                 (disk0 state' ?|= eq (diskUpd d a' b) /\
                  disk1 state' ?|= eq d) \/
                 (disk0 state' ?|= eq d /\
                  disk1 state' ?|= eq d);
           |})
        (fixup a)
        td.recover
        td.abstr.
  Proof.
    unfold fixup; intros.
    step.

    destruct r; try step.

    destruct r; try step.
    destruct (v == v0); subst; try step.

    simplify.
    simplify.
  Qed.

  (* To make these specifications precise while also covering both the already
   * synced and diverged disks cases, we keep track of which input state we're
   * in from the input and use it to give an exact postcondition. *)
  Inductive DiskStatus :=
  | FullySynced
  | OutOfSync (a:addr) (b:block).

  Theorem fixup_ok : forall a,
      proc_spec
        (fun '(d, s) state =>
           {|
             pre :=
               a < diskSize d /\
               match s with
               | FullySynced => disk0 state ?|= eq d /\
                                disk1 state ?|= eq d
               | OutOfSync a' b => a' <= a /\
                                   disk0 state ?|= eq (diskUpd d a' b) /\
                                   disk1 state ?|= eq d
               end;
             post :=
               fun r state' =>
                 match s with
                 | FullySynced => disk0 state' ?|= eq d /\
                                  disk1 state' ?|= eq d
                 | OutOfSync a' b =>
                   match r with
                   | Continue =>
                     (a' < a /\
                      disk0 state' ?|= eq (diskUpd d a' b) /\
                      disk1 state' ?|= eq d) \/
                     (disk0 state' ?|= eq (diskUpd d a' b) /\
                      disk1 state' ?|= eq (diskUpd d a' b))
                   | RepairDone =>
                     (disk0 state' ?|= eq d /\
                      disk1 state' ?|= eq d) \/
                     (disk0 state' ?|= eq (diskUpd d a' b) /\
                      disk1 state' ?|= eq (diskUpd d a' b))
                   end
                 end;
             recovered :=
               fun _ state' =>
                 match s with
                 | FullySynced => disk0 state' ?|= eq d /\
                                  disk1 state' ?|= eq d
                 | OutOfSync a' b =>
                   (disk0 state' ?|= eq (diskUpd d a' b) /\
                    disk1 state' ?|= eq (diskUpd d a' b)) \/
                   (disk0 state' ?|= eq (diskUpd d a' b) /\
                    disk1 state' ?|= eq d) \/
                   (disk0 state' ?|= eq d /\
                    disk1 state' ?|= eq d)
                 end;
           |})
        (fixup a)
        td.recover
        td.abstr.
  Proof.
    spec_intros; simplify.
    rename_by_type DiskStatus s.
    destruct s; intuition eauto.
    - spec_case fixup_equal_ok; simplify; finish.
      descend; (intuition eauto); destruct matches in *;
        intuition eauto.
    - apply PeanoNat.Nat.lt_eq_cases in H1; intuition.
      + spec_case fixup_wrong_addr_ok; simplify; finish.
        descend; intuition eauto.

        destruct v; intuition eauto.
      + spec_case fixup_correct_addr_ok; simplify; finish.
        descend; intuition eauto.

        destruct v; intuition eauto.
  Qed.

  Hint Resolve fixup_ok.

  Hint Resolve Lt.lt_n_Sm_le.

  Hint Rewrite diskUpd_size : rd.

  Theorem recover_at_ok : forall a,
      proc_spec
        (fun '(d, s) state =>
           {|
             pre :=
               a <= diskSize d /\
               match s with
               | FullySynced => disk0 state ?|= eq d /\
                                disk1 state ?|= eq d
               | OutOfSync a' b => a' < a /\
                                   disk0 state ?|= eq (diskUpd d a' b) /\
                                   disk1 state ?|= eq d
               end;
             post :=
               fun r state' =>
                 match s with
                 | FullySynced =>
                   disk0 state' ?|= eq d /\
                   disk1 state' ?|= eq d
                 | OutOfSync a' b =>
                   (disk0 state' ?|= eq d /\
                    disk1 state' ?|= eq d) \/
                   (disk0 state' ?|= eq (diskUpd d a' b) /\
                    disk1 state' ?|= eq (diskUpd d a' b))
                 end;
             recovered :=
               fun _ state' =>
                 match s with
                 | FullySynced => disk0 state' ?|= eq d /\
                                  disk1 state' ?|= eq d
                 | OutOfSync a' b =>
                   (disk0 state' ?|= eq d /\
                    disk1 state' ?|= eq d) \/
                   (disk0 state' ?|= eq (diskUpd d a' b) /\
                    disk1 state' ?|= eq d) \/
                   (disk0 state' ?|= eq (diskUpd d a' b) /\
                    disk1 state' ?|= eq (diskUpd d a' b))
                 end;
           |})
        (recover_at a)
        td.recover
        td.abstr.
  Proof.
    induction a; simpl; intros.
    - step.
      rename_by_type DiskStatus s.
      destruct s; intuition (subst; eauto); simplify.
      omega.
    - step.
      rename_by_type DiskStatus s.
      destruct s; intuition (subst; eauto).
      rename_by_type disk d.
      exists d, FullySynced; intuition eauto.
      destruct r; step.

      exists d, FullySynced; intuition eauto.
      rename_by_type disk d.
      exists d, (OutOfSync a0 b); intuition eauto.

      destruct r; step.
      intuition.
      exists d, (OutOfSync a0 b); intuition eauto.
      exists (diskUpd d a0 b), FullySynced; intuition eauto.
      simplify; finish.
  Qed.

  Hint Resolve recover_at_ok.

  Definition Recover_spec :=
    (fun '(d, s) state =>
       {|
         pre :=
           match s with
           | FullySynced => disk0 state ?|= eq d /\
                            disk1 state ?|= eq d
           | OutOfSync a b => a < diskSize d /\
                              disk0 state ?|= eq (diskUpd d a b) /\
                              disk1 state ?|= eq d
           end;
         post :=
           fun (_:unit) state' =>
             match s with
             | FullySynced => disk0 state' ?|= eq d /\
                              disk1 state' ?|= eq d
             | OutOfSync a b =>
               (disk0 state' ?|= eq d /\
                disk1 state' ?|= eq d) \/
               (disk0 state' ?|= eq (diskUpd d a b) /\
                disk1 state' ?|= eq (diskUpd d a b))
             end;
         recovered :=
           fun (_:unit) state' =>
             match s with
             | FullySynced => disk0 state' ?|= eq d /\
                              disk1 state' ?|= eq d
             | OutOfSync a b =>
               (disk0 state' ?|= eq d /\
                disk1 state' ?|= eq d) \/
               (disk0 state' ?|= eq (diskUpd d a b) /\
                disk1 state' ?|= eq d) \/
               (disk0 state' ?|= eq (diskUpd d a b) /\
                disk1 state' ?|= eq (diskUpd d a b))
             end;
       |}).

  Theorem Recover_rok :
    proc_spec
      Recover_spec
      (Recover)
      td.recover
      td.abstr.
  Proof.
    unfold Recover, Recover_spec; intros.
    spec_intros; simplify.
    rename_by_type DiskStatus s.
    rename_by_type disk d.
    destruct s; simplify.
    + step.
      step.
      exists d, FullySynced; intuition eauto.

      step.

    + step.
      exists (diskUpd d a b), d; (intuition eauto); simplify.
      step.

      exists d, (OutOfSync a b); intuition eauto.
      step.
  Qed.

  Theorem Recover_ok :
    prog_loopspec
      Recover_spec
      (Recover)
      td.recover
      td.abstr.
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

  Hint Resolve Recover_ok.


  Definition recover: proc unit :=
    _ <- td.recover;
    Recover.


  (**
   * Specifications and proofs about our implementation of the API
   * with our own full recovery.
   *)

  Theorem read_rok : forall a,
    proc_spec
          (fun d state =>
             {|
               pre := disk0 state ?|= eq d /\
                      disk1 state ?|= eq d;
               post :=
                 fun r state' =>
                   diskGet d a ?|= eq r /\
                   disk0 state' ?|= eq d /\
                   disk1 state' ?|= eq d;
               recovered :=
                 fun _ state' =>
                   disk0 state' ?|= eq d /\
                   disk1 state' ?|= eq d;
             |})
    (read a) recover td.abstr.
  Proof.
    unfold recover.
    start.
    rename a0 into d.
    descend; (intuition eauto); simplify.
    exists d, FullySynced; intuition eauto.
  Qed.

  Theorem write_rok : forall a b,
      proc_spec
        (fun d state =>
           {|
             pre :=
               disk0 state ?|= eq d /\
               disk1 state ?|= eq d;
             post :=
               fun r state' =>
                 r = tt /\
                 disk0 state' ?|= eq (diskUpd d a b) /\
                 disk1 state' ?|= eq (diskUpd d a b);
             recovered :=
               fun _ state' =>
                 (disk0 state' ?|= eq d /\
                  disk1 state' ?|= eq d) \/
                 (disk0 state' ?|= eq (diskUpd d a b) /\
                  disk1 state' ?|= eq (diskUpd d a b));
            |})
        (write a b)
        recover
        td.abstr.
  Proof.
    unfold recover.
    start.
    rename a0 into d.
    descend; (intuition eauto); simplify.
    - exists d, FullySynced; intuition eauto.
    - exists d, (OutOfSync a b); intuition eauto.
    - exists (diskUpd d a b), FullySynced; intuition eauto.
   Qed.

  Theorem size_rok :
    proc_spec
      (fun d state =>
         {|
           pre := disk0 state ?|= eq d /\
                  disk1 state ?|= eq d;
           post :=
             fun r state' =>
               r = diskSize d /\
               disk0 state' ?|= eq d /\
               disk1 state' ?|= eq d;
           recovered :=
             fun _ state' =>
               disk0 state' ?|= eq d /\
               disk1 state' ?|= eq d;
         |})
      (size)
      recover
      td.abstr.
  Proof.
    unfold recover.
    start.
    rename a into d.
    exists d, d; (intuition eauto); simplify.
    exists d, FullySynced; intuition eauto.
  Qed.

  Hint Resolve read_rok write_rok size_rok Recover_rok.


  Definition abstraction_f (state: TwoDiskBaseAPI.State) : OneDiskAPI.State :=
    match state with
    | @Disks (Some d) _ _ => d
    | @Disks None (Some d) _ => d
    | _ => empty_disk (* impossible *)
    end.

  Definition rd_invariant (state: TwoDiskBaseAPI.State) :=
    match state with
    | @Disks (Some d_0) (Some d_1) _ =>
      d_0 = d_1
    | _ => True
    end.

  Definition rd_layer_abstraction (state: TwoDiskBaseAPI.State) (state': OneDiskAPI.State) :=
    rd_invariant state /\
    state' = abstraction_f state.

  Definition abstr : Abstraction OneDiskAPI.State :=
    abstraction_compose td.abstr {| abstraction := rd_layer_abstraction; |}.


  (* We re-express the abstraction and invariant's behavior in terms of the
     maybe holds (m ?|= F) statements in all of our specifications. *)

  Ltac crush :=
    intros; repeat match goal with
                   | [ state: TwoDiskBaseAPI.State |- _ ] =>
                     destruct state; simpl in *
                   | _ => destruct matches in *
                   | _ => eauto
                   end.

  Theorem invariant_to_disks_eq0 : forall state,
      rd_invariant state ->
      disk0 state ?|= eq (abstraction_f state).
  Proof.
    crush.
  Qed.

  Theorem invariant_to_disks_eq1 : forall state,
      rd_invariant state ->
      disk1 state ?|= eq (abstraction_f state).
  Proof.
    crush.
  Qed.

  Theorem disks_eq_to_invariant : forall state d,
      disk0 state ?|= eq d ->
      disk1 state ?|= eq d ->
      rd_invariant state.
  Proof.
    crush.
  Qed.

  Theorem disks_eq_to_abstraction : forall state d,
      disk0 state ?|= eq d ->
      disk1 state ?|= eq d ->
      d = abstraction_f state.
  Proof.
    crush.
    solve_false.
  Qed.

  Theorem disks_eq_to_abstraction' : forall state d,
      disk0 state ?|= eq d ->
      disk1 state ?|= eq d ->
      abstraction_f state = d.
  Proof.
    intros.
    symmetry; eauto using disks_eq_to_abstraction.
  Qed.

  Hint Resolve invariant_to_disks_eq0 invariant_to_disks_eq1.
  Hint Resolve
       disks_eq_to_invariant
       disks_eq_to_abstraction
       disks_eq_to_abstraction'.


  Theorem init_ok : init_abstraction init recover abstr inited_any.
  Proof.
    intros.
    eapply then_init_compose; eauto.
    eapply proc_spec_weaken; eauto.
    unfold spec_impl; intros.
    destruct state.
    destruct disk0; destruct disk1; try solve [ exfalso; eauto ].
    - exists (d, d0); simpl; intuition eauto.
      unfold rd_layer_abstraction, rd_invariant, abstraction_f.
      destruct v; repeat deex; eauto.
      destruct state'. destruct disk0; destruct disk1; try solve [ exfalso; eauto ].
      all: eexists; intuition eauto; congruence.
    - exists (d, d); simpl; intuition eauto.
      unfold rd_layer_abstraction, rd_invariant, abstraction_f.
      destruct v; repeat deex; eauto.
      destruct state'. destruct disk0; destruct disk1; try solve [ exfalso; eauto ].
      all: eexists; intuition eauto; congruence.
    - exists (d, d); simpl; intuition eauto.
      unfold rd_layer_abstraction, rd_invariant, abstraction_f.
      destruct v; repeat deex; eauto.
      destruct state'. destruct disk0; destruct disk1; try solve [ exfalso; eauto ].
      all: eexists; intuition eauto; congruence.
  Qed.

  Theorem read_ok : forall a, proc_spec (read_spec a) (read a) recover abstr.
  Proof.
    intros.
    apply spec_abstraction_compose;
      eapply proc_spec_weaken; eauto;
      unfold spec_impl, rd_layer_abstraction; simplify.
    exists (abstraction_f state); (intuition eauto); simplify; finish.
  Qed.

  Theorem write_ok : forall a v, proc_spec (write_spec a v) (write a v) recover abstr.
  Proof.
    intros.
    apply spec_abstraction_compose;
      eapply proc_spec_weaken; eauto;
      unfold spec_impl, rd_layer_abstraction; simplify.
    exists (abstraction_f state); (intuition eauto); simplify; finish.
    exists (abstraction_f state'); intuition eauto.
  Qed.

  Theorem size_ok : proc_spec size_spec size recover abstr.
  Proof.
    intros.
    apply spec_abstraction_compose;
      eapply proc_spec_weaken; eauto;
      unfold spec_impl, rd_layer_abstraction; simplify.
    exists (abstraction_f state); (intuition eauto); simplify; finish.
  Qed.

  Theorem recover_noop : rec_noop recover abstr no_wipe.
  Proof.
    eapply rec_noop_compose; eauto; simpl.
    autounfold; unfold rd_layer_abstraction, Recover_spec; simplify.
    exists (abstraction_f state0), FullySynced; intuition eauto.
    descend; intuition eauto.
  Qed.

End ReplicatedDisk.
