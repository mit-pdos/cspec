Require Import POCS.

Require Import TwoDisk.TwoDiskAPI.
Require Import ReplicatedDisk.ReplicatedDiskAPI.
Require Import ReplicatedDisk.TwoDiskProgSpec.

Module RD.

  Section ReplicatedDisk.

    (* The replicated disk implementation works for any implementation of two
     * disks - [Interface] already captures the implementation and all the
     * correctness proofs needed here. *)
    Variable (td:Interface TD.API).

    (**
     * Implementation of the replicated disk API.
     *)

    Definition Read (a:addr) : prog block :=
      mv0 <- Prim td (TD.Read d0 a);
      match mv0 with
      | Working v => Ret v
      | Failed =>
        mv2 <- Prim td (TD.Read d1 a);
        match mv2 with
        | Working v => Ret v
        | Failed => Ret block0
        end
      end.

    Definition Write (a:addr) (b:block) : prog unit :=
      (* Fill in your implementation here. *)
      (* SOL *)
      _ <- Prim td (TD.Write d0 a b);
      _ <- Prim td (TD.Write d1 a b);
      Ret tt.

    Definition Write_stub (a:addr) (b:block) : prog unit :=
      (* END *)
      Ret tt.

    Definition write_read_check (a : addr) (b : block) : prog block :=
      _ <- Write a b;
      b' <- Read a;
      Ret b'.

    Definition DiskSize : prog nat :=
      msz <- Prim td (TD.DiskSize d0);
      match msz with
      | Working sz => Ret sz
      | Failed =>
        msz <- Prim td (TD.DiskSize d1);
        match msz with
        | Working sz => Ret sz
        | Failed => Ret 0
        end
      end.

    Definition DiskSizeInit : prog (option nat) :=
      sz1 <- Prim td (TD.DiskSize d0);
      sz2 <- Prim td (TD.DiskSize d1);
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

    Fixpoint init_at (a:nat) : prog unit :=
      match a with
      | 0 => Ret tt
      | S a =>
        _ <- Prim td (TD.Write d0 a block0);
        _ <- Prim td (TD.Write d1 a block0);
        init_at a
      end.

    Definition Init : prog InitResult :=
      size <- DiskSizeInit;
      match size with
      | Some sz =>
        _ <- init_at sz;
        Ret Initialized
      | None =>
        Ret InitFailed
      end.


    (**
     * Helper lemmas and tactics for proofs.
     *)

    (* As the final step in giving the correctness of the replicated disk
    operations, we prove recovery specs that include the replicated disk Recover
    function. *)

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
             | _ => progress autounfold with rd in *
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
               | |- prog_spec _ _ _ _ => idtac
               | _ => fail
               end
             end.

    Ltac step :=
      step_prog; simplify; finish.

    Ltac start := intros;
                  match goal with
                  | |- prog_spec _ _ (_ <- _; _) _ =>
                    eapply compose_recovery; eauto; simplify
                  end.

    Hint Unfold TD.wipe : rd.

    Implicit Type (state:TD.State).


    (**
     * Specifications and proofs about our implementation of the replicated disk API,
     * without considering our recovery.
     *)

    Lemma both_disks_not_missing : forall (state: TD.State),
        TD.disk0 state ?|= missing ->
        TD.disk1 state ?|= missing ->
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
               pre := TD.disk0 state ?|= eq d /\
                      TD.disk1 state ?|= eq d;
               post :=
                 fun r state' =>
                   d a ?|= eq r /\
                   TD.disk0 state' ?|= eq d /\
                   TD.disk1 state' ?|= eq d;
               recover :=
                 fun _ state' =>
                   TD.disk0 state' ?|= eq d /\
                   TD.disk1 state' ?|= eq d;
             |})
          (Read a)
          (irec td)
          (interface_abs td).
    Proof.
      unfold Read.

      step.

      destruct r; step.
      destruct r; step.
    Qed.

    Hint Resolve Read_ok.


    Theorem Write_ok : forall a b,
        prog_spec
          (fun d state =>
             {|
               pre :=
                 TD.disk0 state ?|= eq d /\
                 TD.disk1 state ?|= eq d;
               post :=
                 fun r state' =>
                   r = tt /\
                   (* Fill in your postcondition here *)
                   (* SOL *)
                   TD.disk0 state' ?|= eq (diskUpd d a b) /\
                   TD.disk1 state' ?|= eq (diskUpd d a b);
                   (* END *)
                   (* STUB: True; *)
               recover :=
                 fun _ state' =>
                   (* Fill in your recovery condition here *)
                   (* SOL *)
                   (TD.disk0 state' ?|= eq d /\
                    TD.disk1 state' ?|= eq d) \/
                   (a < size d /\
                    TD.disk0 state' ?|= eq (diskUpd d a b) /\
                    TD.disk1 state' ?|= eq d) \/
                   (TD.disk0 state' ?|= eq (diskUpd d a b) /\
                    TD.disk1 state' ?|= eq (diskUpd d a b));
                   (* END *)
                   (* STUB: True; *)
             |})
          (Write a b)
          (irec td)
          (interface_abs td).
    Proof.
      unfold Write.

      step.

      (* Prove your write implementation meets your postcondition and recovery condition. *)
      (* SOL *)
      destruct r; step.
      descend; intuition eauto.

      step.
      destruct r; (intuition eauto); simplify.
      destruct (lt_dec a (size a')).
      eauto 10.
      autorewrite with upd in *; eauto.

      destruct r; step.
      (* END *)
    Qed.

    Hint Resolve Write_ok.


    Theorem write_read_check_ok : forall a b,
        prog_spec
          (fun d state =>
             {|
               pre :=
                 a < size d /\
                 TD.disk0 state ?|= eq d /\
                 TD.disk1 state ?|= eq d;
               post :=
                 fun r state' =>
                   r = b /\
                   TD.disk0 state' ?|= eq (diskUpd d a b) /\
                   TD.disk1 state' ?|= eq (diskUpd d a b);
               recover :=
                 fun _ state' =>
                   True;
             |})
          (write_read_check a b)
          (irec td)
          (interface_abs td).
    Proof.
      unfold write_read_check.
      step.
      step.
      step.
      autorewrite with upd in *.
      congruence.
    Qed.

    Hint Resolve write_read_check_ok.


    Theorem DiskSize_ok :
      prog_spec
        (fun '(d_0, d_1) state =>
           {|
             pre :=
               TD.disk0 state ?|= eq d_0 /\
               TD.disk1 state ?|= eq d_1 /\
               size d_0 = size d_1;
             post :=
               fun r state' =>
                 r = size d_0 /\
                 r = size d_1 /\
                 TD.disk0 state' ?|= eq d_0 /\
                 TD.disk1 state' ?|= eq d_1;
             recover :=
               fun _ state' =>
                 TD.disk0 state' ?|= eq d_0 /\
                 TD.disk1 state' ?|= eq d_1;
           |})
        (DiskSize)
        (irec td)
        (interface_abs td).
    Proof.
      unfold DiskSize.

      step.

      destruct r; step.
      destruct r; step.
    Qed.

    Hint Resolve DiskSize_ok.


    Definition equal_after a (d_0 d_1: disk) :=
      size d_0 = size d_1 /\
      forall a', a <= a' -> d_0 a' = d_1 a'.

    Lemma le_eq_or_S_le : forall n m,
        n <= m ->
        n = m \/
        S n <= m /\ n <> m.
    Proof.
      intros.
      omega.
    Qed.

    Lemma equal_after_diskUpd : forall a d_0 d_1 b,
        equal_after (S a) d_0 d_1 ->
        equal_after a (diskUpd d_0 a b) (diskUpd d_1 a b).
    Proof.
      unfold equal_after; intuition.
      autorewrite with upd; eauto.
      apply le_eq_or_S_le in H; intuition subst.
      destruct (lt_dec a' (size d_0)); autorewrite with upd.
      assert (a' < size d_1) by congruence; autorewrite with upd; auto.
      assert (~a' < size d_1) by congruence; autorewrite with upd; auto.
      autorewrite with upd; eauto.
    Qed.
    Hint Resolve equal_after_diskUpd.

    Theorem init_at_ok : forall a,
        prog_spec
          (fun '(d_0, d_1) state =>
             {| pre :=
                  TD.disk0 state ?|= eq d_0 /\
                  TD.disk1 state ?|= eq d_1 /\
                  equal_after a d_0 d_1;
                post :=
                  fun _ state' =>
                    exists d_0' d_1',
                      TD.disk0 state' ?|= eq d_0' /\
                      TD.disk1 state' ?|= eq d_1' /\
                      equal_after 0 d_0' d_1';
                recover :=
                  fun _ state' => True;
             |})
          (init_at a)
          (irec td)
          (interface_abs td).
    Proof.
      induction a; simpl; intros.
      - step.
      - step.

        step.
        destruct r; finish.
        + step.
          destruct r; simplify; finish.
          (* TODO: why does the hint not trigger here? *)
          descend; intuition eauto using equal_after_diskUpd.
        + step.
          destruct r; finish.
          descend; intuition eauto using equal_after_diskUpd.
          descend; intuition eauto using equal_after_diskUpd.

          Grab Existential Variables.
          exact block0.
    Qed.

    Hint Resolve init_at_ok.


    Theorem DiskSizeInit_ok :
        prog_spec
          (fun '(d_0, d_1) state =>
             {| pre :=
                  TD.disk0 state ?|= eq d_0 /\
                  TD.disk1 state ?|= eq d_1;
                post :=
                  fun r state' =>
                    exists d_0' d_1',
                      TD.disk0 state' ?|= eq d_0' /\
                      TD.disk1 state' ?|= eq d_1' /\
                      match r with
                      | Some sz => size d_0' = sz /\ size d_1' = sz
                      | None => True
                      end;
                recover :=
                  fun _ state' => True;
             |})
          (DiskSizeInit)
          (irec td)
          (interface_abs td).
    Proof.
      unfold DiskSizeInit.
      step.
      step.
      destruct r; descend; intuition eauto.
      - destruct r; try step.
        destruct (v == v0); step.
      - destruct r; step.
    Qed.

    Hint Resolve DiskSizeInit_ok.


    Lemma equal_after_0_to_eq : forall d_0 d_1,
        equal_after 0 d_0 d_1 ->
        d_0 = d_1.
    Proof.
      unfold equal_after; intuition.
      eapply diskMem_ext_eq.
      extensionality a'.
      eapply H1; omega.
    Qed.

    Lemma equal_after_size : forall d_0 d_1,
        size d_0 = size d_1 ->
        equal_after (size d_0) d_0 d_1.
    Proof.
      unfold equal_after; intuition.
      assert (~a' < size d_0) by omega.
      assert (~a' < size d_1) by congruence.
      autorewrite with upd; eauto.
    Qed.

    Hint Resolve equal_after_size.
    Hint Resolve equal_after_0_to_eq.

    Theorem Init_ok :
        prog_spec
          (fun '(d_0, d_1) state =>
             {| pre :=
                  TD.disk0 state ?|= eq d_0 /\
                  TD.disk1 state ?|= eq d_1;
                post :=
                  fun r state' =>
                    match r with
                    | Initialized =>
                      exists d_0' d_1',
                      TD.disk0 state' ?|= eq d_0' /\
                      TD.disk1 state' ?|= eq d_1' /\
                      d_0' = d_1'
                    | InitFailed =>
                      True
                    end;
                recover :=
                  fun _ state' => True;
             |})
          (Init)
          (irec td)
          (interface_abs td).
    Proof.
      unfold Init.
      step.
      descend; intuition eauto.
      destruct r; step.
      step.
    Qed.

    Hint Resolve Init_ok.


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

    Definition fixup (a:addr) : prog RecStatus :=
      mv0 <- Prim td (TD.Read d0 a);
      match mv0 with
      | Working v =>
        mv2 <- Prim td (TD.Read d1 a);
        match mv2 with
        | Working v' =>
          if v == v' then
            Ret Continue
          else
            mu <- Prim td (TD.Write d1 a v);
            Ret (match mu with
                 | Working _ => RepairDoneOrFailed
                 | Failed => RepairDoneOrFailed
                 end)
        | Failed => Ret RepairDoneOrFailed
        end
      | Failed => Ret RepairDoneOrFailed
      end.

    (* recursively performs recovery at [a-1], [a-2], down to 0 *)
    Fixpoint recover_at (a:addr) : prog unit :=
      match a with
      | 0 => Ret tt
      | S n =>
        s <- fixup n;
        match s with
        | Continue => recover_at n
        | RepairDoneOrFailed => Ret tt
        end
      end.

    Definition Recover : prog unit :=
      sz <- DiskSize;
      _ <- recover_at sz;
      Ret tt.


    (**
     * Lemmas and recovery proofs.
     *)

    Lemma if_lt_dec : forall A n m (a a':A),
        n < m ->
        (if lt_dec n m then a else a') = a.
    Proof.
      intros.
      destruct (lt_dec n m); auto.
      contradiction.
    Qed.

    Lemma disks_eq_inbounds : forall T (d: diskOf T) a v v',
        a < size d ->
        d a ?|= eq v ->
        d a ?|= eq v' ->
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
        prog_spec
          (fun d state =>
             {|
               pre :=
                 (* for simplicity we only consider in-bounds addresses, though
                    if a is out-of-bounds fixup just might uselessly write to
                    disk and not do anything *)
                 a < size d /\
                 TD.disk0 state ?|= eq d /\
                 TD.disk1 state ?|= eq d;
               post :=
                 fun r state' =>
                   match r with
                   | Continue =>
                     TD.disk0 state' ?|= eq d /\
                     TD.disk1 state' ?|= eq d
                   | RepairDoneOrFailed =>
                     TD.disk0 state' ?|= eq d /\
                     TD.disk1 state' ?|= eq d
                   end;
               recover :=
                 fun _ state' =>
                   TD.disk0 state' ?|= eq d /\
                   TD.disk1 state' ?|= eq d;
             |})
          (fixup a)
          (irec td)
          (interface_abs td).
    Proof.
      unfold fixup.
      step.

      destruct r; step.

      destruct r; try step.
      is_eq v v0; try step.
      assert (v = v0) by eauto using disks_eq_inbounds.
      contradiction.
    Qed.

    Lemma diskUpd_maybe_same : forall (d:disk) a b,
        d a ?|= eq b ->
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
        prog_spec
          (fun '(d, b) state =>
             {|
               pre :=
                 a < size d /\
                 TD.disk0 state ?|= eq (diskUpd d a b) /\
                 TD.disk1 state ?|= eq d;
               post :=
                 fun r state' =>
                   match r with
                   | Continue =>
                     (* could happen if b already happened to be value *)
                     TD.disk0 state' ?|= eq (diskUpd d a b) /\
                     TD.disk1 state' ?|= eq (diskUpd d a b)
                   | RepairDoneOrFailed =>
                     TD.disk0 state' ?|= eq (diskUpd d a b) /\
                     TD.disk1 state' ?|= eq (diskUpd d a b) \/
                     TD.disk0 state' ?|= eq d /\
                     TD.disk1 state' ?|= eq d
                   end;
               recover :=
                 fun _ state' =>
                   (TD.disk0 state' ?|= eq (diskUpd d a b) /\
                    TD.disk1 state' ?|= eq (diskUpd d a b)) \/
                   (TD.disk0 state' ?|= eq (diskUpd d a b) /\
                    TD.disk1 state' ?|= eq d) \/
                   (TD.disk0 state' ?|= eq d /\
                    TD.disk1 state' ?|= eq d);
             |})
          (fixup a)
          (irec td)
          (interface_abs td).
    Proof.
      unfold fixup; intros.
      step.

      destruct r; try step.

      destruct r; try step.
      is_eq b v; try step.

      step.
      destruct r; (intuition eauto); simplify; finish.
    Qed.

    Hint Resolve PeanoNat.Nat.lt_neq.
    Hint Rewrite diskUpd_neq : rd.
    Hint Resolve disks_eq_inbounds.

    Theorem fixup_wrong_addr_ok : forall a,
        prog_spec
          (fun '(d, b, a') state =>
             {|
               pre :=
                 a < size d /\
                 (* recovery, working from end of disk, has not yet reached the
                    correct address *)
                 a' < a /\
                 TD.disk0 state ?|= eq (diskUpd d a' b) /\
                 TD.disk1 state ?|= eq d;
               post :=
                 fun r state' =>
                   match r with
                   | Continue =>
                     TD.disk0 state' ?|= eq (diskUpd d a' b) /\
                     TD.disk1 state' ?|= eq d
                   | RepairDoneOrFailed =>
                     TD.disk0 state' ?|= eq d /\
                     TD.disk1 state' ?|= eq d \/
                     TD.disk0 state' ?|= eq (diskUpd d a' b) /\
                     TD.disk1 state' ?|= eq (diskUpd d a' b)
                   end;
               recover :=
                 fun _ state' =>
                   (TD.disk0 state' ?|= eq (diskUpd d a' b) /\
                    TD.disk1 state' ?|= eq d) \/
                   (TD.disk0 state' ?|= eq d /\
                    TD.disk1 state' ?|= eq d);
             |})
          (fixup a)
          (irec td)
          (interface_abs td).
    Proof.
      unfold fixup; intros.
      step.

      destruct r; try step.

      destruct r; try step.
      is_eq v v0; try step.
    Qed.

    (* To make these specifications precise while also covering both the already
     * synced and diverged disks cases, we keep track of which input state we're
     * in from the input and use it to give an exact postcondition. *)
    Inductive DiskStatus :=
    | FullySynced
    | OutOfSync (a:addr) (b:block).

    Theorem fixup_ok : forall a,
        prog_spec
          (fun '(d, s) state =>
             {|
               pre :=
                 a < size d /\
                 match s with
                 | FullySynced => TD.disk0 state ?|= eq d /\
                                 TD.disk1 state ?|= eq d
                 | OutOfSync a' b => a' <= a /\
                                    TD.disk0 state ?|= eq (diskUpd d a' b) /\
                                    TD.disk1 state ?|= eq d
                 end;
               post :=
                 fun r state' =>
                   match s with
                   | FullySynced => TD.disk0 state' ?|= eq d /\
                                   TD.disk1 state' ?|= eq d
                   | OutOfSync a' b =>
                     match r with
                     | Continue =>
                       (a' < a /\
                        TD.disk0 state' ?|= eq (diskUpd d a' b) /\
                        TD.disk1 state' ?|= eq d) \/
                       (TD.disk0 state' ?|= eq (diskUpd d a' b) /\
                        TD.disk1 state' ?|= eq (diskUpd d a' b))
                     | RepairDone =>
                       (TD.disk0 state' ?|= eq d /\
                        TD.disk1 state' ?|= eq d) \/
                       (TD.disk0 state' ?|= eq (diskUpd d a' b) /\
                        TD.disk1 state' ?|= eq (diskUpd d a' b))
                     end
                   end;
               recover :=
                 fun _ state' =>
                   match s with
                   | FullySynced => TD.disk0 state' ?|= eq d /\
                                   TD.disk1 state' ?|= eq d
                   | OutOfSync a' b =>
                     (TD.disk0 state' ?|= eq (diskUpd d a' b) /\
                      TD.disk1 state' ?|= eq (diskUpd d a' b)) \/
                     (TD.disk0 state' ?|= eq (diskUpd d a' b) /\
                      TD.disk1 state' ?|= eq d) \/
                     (TD.disk0 state' ?|= eq d /\
                      TD.disk1 state' ?|= eq d)
                   end;
             |})
          (fixup a)
          (irec td)
          (interface_abs td).
    Proof.
      spec_cases; simplify.
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
        prog_spec
          (fun '(d, s) state =>
             {|
               pre :=
                 a <= size d /\
                 match s with
                 | FullySynced => TD.disk0 state ?|= eq d /\
                                 TD.disk1 state ?|= eq d
                 | OutOfSync a' b => a' < a /\
                                    TD.disk0 state ?|= eq (diskUpd d a' b) /\
                                    TD.disk1 state ?|= eq d
                 end;
               post :=
                 fun r state' =>
                   match s with
                   | FullySynced =>
                     TD.disk0 state' ?|= eq d /\
                     TD.disk1 state' ?|= eq d
                   | OutOfSync a' b =>
                     (TD.disk0 state' ?|= eq d /\
                      TD.disk1 state' ?|= eq d) \/
                     (TD.disk0 state' ?|= eq (diskUpd d a' b) /\
                      TD.disk1 state' ?|= eq (diskUpd d a' b))
                   end;
               recover :=
                 fun _ state' =>
                   match s with
                   | FullySynced => TD.disk0 state' ?|= eq d /\
                                   TD.disk1 state' ?|= eq d
                   | OutOfSync a' b =>
                     (TD.disk0 state' ?|= eq d /\
                      TD.disk1 state' ?|= eq d) \/
                     (TD.disk0 state' ?|= eq (diskUpd d a' b) /\
                      TD.disk1 state' ?|= eq d) \/
                     (TD.disk0 state' ?|= eq (diskUpd d a' b) /\
                      TD.disk1 state' ?|= eq (diskUpd d a' b))
                   end;
             |})
          (recover_at a)
          (irec td)
          (interface_abs td).
    Proof.
      induction a; simpl; intros.
      - step.
        destruct s; intuition (subst; eauto).
        omega.
      - step.
        destruct s; intuition (subst; eauto).
        exists d, FullySynced; intuition eauto.
        destruct r; step.

        exists d, FullySynced; intuition eauto.
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
             | FullySynced => TD.disk0 state ?|= eq d /\
                             TD.disk1 state ?|= eq d
             | OutOfSync a b => a < size d /\
                               TD.disk0 state ?|= eq (diskUpd d a b) /\
                               TD.disk1 state ?|= eq d
             end;
           post :=
             fun (_:unit) state' =>
               match s with
               | FullySynced => TD.disk0 state' ?|= eq d /\
                               TD.disk1 state' ?|= eq d
               | OutOfSync a b =>
                 (TD.disk0 state' ?|= eq d /\
                  TD.disk1 state' ?|= eq d) \/
                 (TD.disk0 state' ?|= eq (diskUpd d a b) /\
                  TD.disk1 state' ?|= eq (diskUpd d a b))
               end;
           recover :=
             fun (_:unit) state' =>
               match s with
               | FullySynced => TD.disk0 state' ?|= eq d /\
                               TD.disk1 state' ?|= eq d
               | OutOfSync a b =>
                 (TD.disk0 state' ?|= eq d /\
                  TD.disk1 state' ?|= eq d) \/
                 (TD.disk0 state' ?|= eq (diskUpd d a b) /\
                  TD.disk1 state' ?|= eq d) \/
                 (TD.disk0 state' ?|= eq (diskUpd d a b) /\
                  TD.disk1 state' ?|= eq (diskUpd d a b))
               end;
         |}).

    Theorem Recover_rok :
      prog_spec
        Recover_spec
        (Recover)
        (irec td)
        (interface_abs td).
    Proof.
      unfold Recover, Recover_spec; intros.
      step.
      destruct s; simplify.
      + exists d, d; intuition eauto.
        step.
        exists d, FullySynced; intuition eauto.

        step.
      + exists (diskUpd d a b), d; (intuition eauto); simplify.
        step.

        exists d, (OutOfSync a b); intuition eauto.
        step.
    Qed.

    Theorem Recover_ok :
      prog_loopspec
        Recover_spec
        (Recover)
        (irec td)
        (interface_abs td).
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


    (**
     * Specifications and proofs about our implementation of the API
     * with our own full recovery.
     *)

    Theorem Read_rok : forall a,
        prog_spec
          (fun d state =>
             {|
               pre := TD.disk0 state ?|= eq d /\
                      TD.disk1 state ?|= eq d;
               post :=
                 fun r state' =>
                   d a ?|= eq r /\
                   TD.disk0 state' ?|= eq d /\
                   TD.disk1 state' ?|= eq d;
               recover :=
                 fun _ state' =>
                   TD.disk0 state' ?|= eq d /\
                   TD.disk1 state' ?|= eq d;
             |})
          (Read a) (_ <- irec td; Recover)
          (interface_abs td).
    Proof.
      start.
      rename a0 into d.
      descend; (intuition eauto); simplify.
      exists d, FullySynced; intuition eauto.
    Qed.

    Theorem Write_rok : forall a b,
        prog_spec
          (fun d state =>
             {|
               pre :=
                 TD.disk0 state ?|= eq d /\
                 TD.disk1 state ?|= eq d;
               post :=
                 fun r state' =>
                   r = tt /\
                   (* Fill in the postcondition for write; just a copy
                    * of [Write_ok]'s postcondition *)
                   (* SOL *)
                   TD.disk0 state' ?|= eq (diskUpd d a b) /\
                   TD.disk1 state' ?|= eq (diskUpd d a b);
                   (* END *)
                   (* STUB: True; *)
               recover :=
                 fun _ state' =>
                   (* Fill in the recovery condition for write AFTER our recovery.
                    *)
                   (* SOL *)
                   (TD.disk0 state' ?|= eq d /\
                    TD.disk1 state' ?|= eq d) \/
                   (TD.disk0 state' ?|= eq (diskUpd d a b) /\
                    TD.disk1 state' ?|= eq (diskUpd d a b));
                   (* END *)
                   (* STUB: True; *)
             |})
          (Write a b) (_ <- irec td; Recover)
          (interface_abs td).
    Proof.
      start.
      rename a0 into d.

      (* Fill in your proof here. *)
      (* SOL *)
      descend; (intuition eauto); simplify.
      - exists d, FullySynced; intuition eauto.
      - exists d, (OutOfSync a b); intuition eauto.
      - exists (diskUpd d a b), FullySynced; intuition eauto.
      (* END *)
      (* STUB: pocs_admit. *)
    Qed.

    Theorem DiskSize_rok :
      prog_spec
        (fun d state =>
           {|
             pre := TD.disk0 state ?|= eq d /\
                    TD.disk1 state ?|= eq d;
             post :=
               fun r state' =>
                 r = size d /\
                 TD.disk0 state' ?|= eq d /\
                 TD.disk1 state' ?|= eq d;
             recover :=
               fun _ state' =>
                 TD.disk0 state' ?|= eq d /\
                 TD.disk1 state' ?|= eq d;
           |})
        (DiskSize) (_ <- irec td; Recover)
        (interface_abs td).
    Proof.
      start.
      rename a into d.
      exists d, d; (intuition eauto); simplify.
      exists d, FullySynced; intuition eauto.
    Qed.

    (* Now we gather up the implementation and all the correctness proofs,
     * expressing them in terms of the high-level API in D.API. *)

    (* First, we prove some lemmas that re-express the D.API semantics in more
     * convenient terms (in some cases, just for the sake of the automation). *)

    Lemma read_step : forall a (state state':RD.State) b,
        state a ?|= eq b ->
        state' = state ->
        RD.step (RD.Read a) state b state'.
    Proof.
      intros; subst.
      constructor; auto.
      intros.
      replace (state a) in *; auto.
    Qed.

    Lemma write_step : forall a b (state state':RD.State) u,
        state' = diskUpd state a b ->
        RD.step (RD.Write a b) state u state'.
    Proof.
      intros; subst.
      destruct u.
      econstructor; eauto.
    Qed.

    Lemma disk_size_step : forall (state state':RD.State) r,
        r = size state ->
        state' = state ->
        RD.step (RD.DiskSize) state r state'.
    Proof.
      intros; subst.
      econstructor; eauto.
    Qed.

    Hint Resolve read_step write_step disk_size_step.


    (**
     * The proof will require a refinement; we build one up based on the two
     * disk state.
     *)

    Definition abstraction_f (state:TD.State) : RD.State :=
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

    Definition rd_layer_abstraction (state:TD.State) (state':RD.State) :=
      rd_invariant state /\
      state' = abstraction_f state.

    (* We re-express the abstraction and invariant's behavior in terms of the
       maybe holds (m ?|= F) statements in all of our specifications. *)

    Ltac crush :=
      intros; repeat match goal with
                     | [ state: TD.State |- _ ] =>
                       destruct state; simpl in *
                     | _ => destruct matches in *
                     | _ => eauto
                     end.

    Lemma invariant_to_disks_eq0 : forall state,
        rd_invariant state ->
        TD.disk0 state ?|= eq (abstraction_f state).
    Proof.
      crush.
    Qed.

    Lemma invariant_to_disks_eq1 : forall state,
        rd_invariant state ->
        TD.disk1 state ?|= eq (abstraction_f state).
    Proof.
      crush.
    Qed.

    Lemma disks_eq_to_invariant : forall state d,
        TD.disk0 state ?|= eq d ->
        TD.disk1 state ?|= eq d ->
        rd_invariant state.
    Proof.
      crush.
    Qed.

    Lemma disks_eq_to_abstraction : forall state d,
        TD.disk0 state ?|= eq d ->
        TD.disk1 state ?|= eq d ->
        d = abstraction_f state.
    Proof.
      crush.
      solve_false.
    Qed.

    Lemma disks_eq_to_abstraction' : forall state d,
        TD.disk0 state ?|= eq d ->
        TD.disk1 state ?|= eq d ->
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

    (* Finally, we put together the pieces of the [Interface]. Here we also
     * convert from our specificatiosn above to the exact form that an Interface
     * uses; the proofs are automatic after defining the lemmas above about D.step
     * and the layer refinement. *)

    Definition d_op_impl T (op:RD.Op T) : prog T :=
      match op with
      | RD.Read a => Read a
      | RD.Write a b => Write a b
      | RD.DiskSize => DiskSize
      end.

    Definition rd_abstraction : Abstraction RD.State :=
      abstraction_compose
        (interface_abs td)
        {| abstraction := rd_layer_abstraction; |}.

    Definition impl : InterfaceImpl RD.Op :=
      {| op_impl := d_op_impl;
         recover_impl := _ <- irec td; Recover;
      init_impl := then_init (iInit td) (Init) |}.

    Hint Resolve Read_rok Write_rok DiskSize_rok Recover_rok.

    Theorem state_some_disks : forall state,
        exists d_0 d_1,
          TD.disk0 state ?|= eq d_0 /\
          TD.disk1 state ?|= eq d_1.
    Proof.
      destruct state.
      destruct disk0, disk1; simpl; eauto.
      exfalso; eauto.
    Qed.

    Theorem rd_crash_effect_valid :
      crash_effect_valid {| abstraction := rd_layer_abstraction; |}
                         TD.wipe (fun (state state':RD.State) => state' = state).
    Proof.
      econstructor; unfold TD.wipe; intuition (subst; eauto).
    Qed.

    Theorem rd_layer_abstraction_f : forall state,
        rd_invariant state ->
        rd_layer_abstraction state (abstraction_f state).
    Proof.
      unfold rd_layer_abstraction; intuition.
    Qed.

    Hint Resolve rd_layer_abstraction_f.

    Definition rd : Interface RD.API.
      unshelve econstructor.
      - exact impl.
      - exact rd_abstraction.
      - intros.
        destruct op; unfold op_spec;
          apply spec_abstraction_compose;
          eapply prog_spec_weaken; eauto;
            unfold spec_impl, rd_layer_abstraction; simplify.
        + exists (abstraction_f state); (intuition eauto); simplify; finish.
        + exists (abstraction_f state); (intuition eauto); simplify; finish.
          exists (abstraction_f state'); intuition eauto.
          right; descend; intuition eauto.
        + exists (abstraction_f state); (intuition eauto); simplify.
          descend; intuition eauto.
          descend; intuition eauto.
      - eapply rec_noop_compose; eauto; simpl.
        unfold TD.wipe, rd_layer_abstraction, Recover_spec; simplify.
        exists (abstraction_f state0), FullySynced; intuition eauto.
        descend; intuition eauto.
      - eapply then_init_compose; eauto.
        eapply prog_spec_weaken; unfold spec_impl; simplify.
        eauto.
        pose proof (state_some_disks state); simplify.
        descend; intuition eauto.
        destruct v; simplify; finish.

        Grab Existential Variables.
        all: auto.
    Defined.

  End ReplicatedDisk.

End RD.

Print Assumptions RD.rd.
