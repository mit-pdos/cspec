Require Import Omega.

Require Import Automation.
Require Import Disk.AsyncDisk.

Require Import Refinement.Interface.
Require Import Refinement.ProgLang.Prog.
Require Import Refinement.ProgLang.Hoare.
Require Import
        TwoDisk.AsyncTwoDiskAPI
        TwoDisk.AsyncTwoDiskTheorems
        TwoDisk.TwoDiskFacts.
Require Import SeqDisk.AsyncReplicatedDisk.Step.

Require Import MaybeHolds.

Section Init.

  Variable (td:Interface TD.API).

  Fixpoint init_at (a:nat) : proc unit :=
    match a with
    | 0 => Ret tt
    | S a => _ <- Prim td (TD.Write d0 a block0);
              _ <- Prim td (TD.Write d1 a block0);
              init_at a
    end.

  Definition DiskSizes : proc (nat * nat + nat) :=
    sz1 <- Prim td (TD.DiskSize d0);
      match sz1 with
      | Working sz1 => sz2 <- Prim td (TD.DiskSize d1);
                        match sz2 with
                        | Working sz2 => if sz1 == sz2 then
                                          Ret (inr sz1)
                                        else Ret (inl (sz1, sz2))
                        | Failed => Ret (inr sz1)
                        end
      | Failed => sz2 <- Prim td (TD.DiskSize d1);
                   match sz2 with
                   | Working sz2 => Ret (inr sz2)
                   | Failed => Ret (inl (0, 0)) (* impossible *)
                   end
      end.

  Definition Init : proc InitResult :=
    sizes <- DiskSizes;
      match sizes with
      | inr sz => _ <- init_at sz;
                   _ <- Prim td (TD.Sync d0);
                   _ <- Prim td (TD.Sync d1);
                   Ret Initialized
      | inl _ => Ret InitFailed
      end.

  Theorem le_eq_or_S_le : forall n m,
      n <= m ->
      n = m \/
      S n <= m /\ n <> m.
  Proof.
    intros.
    omega.
  Qed.

  Definition equal_after a (d_0 d_1: histdisk) :=
    size d_0 = size d_1 /\
    forall a', a <= a' -> match d_0 a', d_1 a' with
                   | Some b0, Some b1 => curr_val b0 = curr_val b1
                   | _, _ => True
                   end.

  Theorem equal_after_diskUpdF : forall a d_0 d_1 b,
      equal_after (S a) d_0 d_1 ->
      equal_after a (diskUpdF d_0 a (buffer b)) (diskUpdF d_1 a (buffer b)).
  Proof.
    unfold equal_after; intuition.
    autorewrite with upd; eauto.
    apply le_eq_or_S_le in H; intuition subst.
    - destruct (lt_dec a' (size d_0)); autorewrite with upd; auto.
      assert (a' < size d_1) by congruence.
      pose proof (@diskUpdF_inbounds _ d_0 a' (buffer b)).
      pose proof (@diskUpdF_inbounds _ d_1 a' (buffer b)).
      intuition; repeat deex; repeat simpl_match.
      autorewrite with block; auto.
    - autorewrite with upd.
      specialize (H1 a'); intuition.
  Qed.

  Hint Resolve equal_after_diskUpdF.

  Theorem init_at_ok : forall a,
      proc_spec
        (fun '(d_0, d_1) state =>
           {| pre :=
                TD.disk0 state |= covered d_0 /\
                TD.disk1 state |= covered d_1 /\
                equal_after a d_0 d_1;
              post :=
                fun _ state' =>
                  exists d_0' d_1',
                    TD.disk0 state' |= covered d_0' /\
                    TD.disk1 state' |= covered d_1' /\
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
        descend; intuition eauto using equal_after_diskUpdF.
      + step.
        destruct r; finish.
        descend; intuition eauto using equal_after_diskUpdF.
        descend; intuition eauto using equal_after_diskUpdF.

        Grab Existential Variables.
        exact block0.
  Qed.

  Hint Resolve init_at_ok.

  Hint Resolve both_disks_not_missing : false.

  Theorem DiskSizes_ok :
      proc_spec
        (fun '(d_0, d_1) state =>
           {| pre :=
                TD.disk0 state |= covered d_0 /\
                TD.disk1 state |= covered d_1;
              post :=
                fun r state' =>
                  exists d_0' d_1',
                    TD.disk0 state' |= covered d_0' /\
                    TD.disk1 state' |= covered d_1' /\
                    match r with
                    | inr sz => size d_0' = sz /\
                               size d_1' = sz
                    | inl _ => size d_0 <> size d_1
                    end;
              recover :=
                fun _ state' => True;
           |})
        (DiskSizes)
        (irec td)
        (interface_abs td).
  Proof.
    unfold DiskSizes; step.
    destruct r; step.
    destruct r; try step.
    is_eq (size d_0) v; step.
    destruct r; step.
  Qed.

  Theorem equal_after_0_to_eq : forall d_0 d_1,
      equal_after 0 d_0 d_1 ->
      forall a, match d_0 a, d_1 a with
           | Some b0, Some b1 => curr_val b0 = curr_val b1
           | None, None => True
           | _, _ => False
           end.
  Proof.
    unfold equal_after; intuition.
    specialize (H1 a ltac:(omega)).
    destruct matches in *;
      eauto using same_size_disks_not_different.
  Qed.

  Theorem equal_after_size : forall d_0 d_1,
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

  Theorem equal_curr_after_flush : forall d_0 d_1,
      equal_after 0 d_0 d_1 ->
      flush d_0 = flush d_1.
  Proof.
    intros.
    eapply diskMem_ext_eq.
    extensionality a.
    simpl.
    eapply equal_after_0_to_eq with (a:=a) in H.
    destruct matches in *; try contradiction.
    autorewrite with block in *.
    rewrite H.
    autorewrite with block; auto.
  Qed.

  Hint Resolve DiskSizes_ok.

  Theorem Init_ok :
      proc_spec
        (fun '(d_0, d_1) state =>
           {| pre :=
                TD.disk0 state |= covered d_0 /\
                TD.disk1 state |= covered d_1;
              post :=
                fun r state' =>
                  match r with
                  | Initialized =>
                    exists d, TD.disk0 state' |= covered d /\
                         TD.disk1 state' |= covered d
                  | InitFailed => (size d_0 <> size d_1)%type
                  end;
              recover :=
                fun _ state' => True;
           |})
        (Init)
        (irec td)
        (interface_abs td).
  Proof.
    unfold Init; step.
    step.
    step.
    step.
    step.
    step.

    eapply pred_weaken in H9; [ | apply then_flush_covered ].
    eapply pred_weaken in H10; [ | apply then_flush_covered ].
    erewrite equal_curr_after_flush in * by eauto.
    eauto.
  Qed.

End Init.

Hint Resolve Init_ok.
