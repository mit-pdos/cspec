Require Import POCS.
Require Import AtomicPairAPI.
Require Import Common.OneDiskAPI.
Import ListNotations.


Module AtomicPair (d : OneDiskAPI) <: AtomicPairAPI.

  (** To implement this API, we suggest you work out a way that does not use
      logging but instead maintains two sets of blocks and a pointer to switch
      between them. You can use [block0] and [block1] as concrete values for the
      pointer and [b == b'] to compare blocks in code. *)

  (* To make implementations more consistent, we recommend this layout (where
  the pointer is in address 0). *)
  Definition ptr_a : addr := 0.
  Definition data0a : addr := 1.
  Definition data1a : addr := 2.
  Definition data0b : addr := 3.
  Definition data1b : addr := 4.

  (* We plug some extra facts into the automation to make the above definitions
  more convenient. You can ignore these; they automatically make [auto] and
  [autorewrite with upd] more powerful. *)

  Ltac addr_omega :=
    progress unfold ptr_a, data0a, data1a, data0b, data1b;
    omega.

  Hint Extern 2 (_ <> _ :> addr) => addr_omega.
  Hint Extern 2 (_ < _) => addr_omega.

  (* EXERCISE (3a): implement this procedure *)
  Definition get : proc (block*block) :=
    (* SOL *)
    ptr <- d.read ptr_a;
      if ptr == block0 then
        b0 <- d.read data0a;
          b1 <- d.read data1a;
          Ret (b0, b1)
      else
        b0 <- d.read data0b;
      b1 <- d.read data1b;
      Ret (b0, b1).
  (* END *)
  (* STUB: Ret (block0, block0). *)

  (* EXERCISE (3a): implement this procedure *)
  Definition put (p : block*block) : proc unit :=
    (* SOL *)
    ptr <- d.read ptr_a;
      if ptr == block0 then
        _ <- d.write data0b (fst p);
          _ <- d.write data1b (snd p);
          _ <- d.write ptr_a block1;
          Ret tt
      else
        _ <- d.write data0a (fst p);
      _ <- d.write data1a (snd p);
      _ <- d.write ptr_a block0;
      Ret tt.
  (* END *)
  (* STUB: Ret tt. *)

  (* EXERCISE (3a): implement this procedure *)
  Definition init' : proc InitResult :=
    (* SOL *)
    len <- d.size;
      if len == 5 then
        _ <- d.write ptr_a block0;
        _ <- d.write data0a block0;
        _ <- d.write data1a block0;
          Ret Initialized
      else Ret InitFailed.
    (* END *)
    (* STUB: Ret InitFailed. *)

  Definition init := then_init d.init init'.

  (* Using this approach with a pointer (as opposed to write-ahead logging), you
  won't need a recovery procedure. *)
  Definition recover: proc unit :=
    d.recover.

  (* EXERCISE (3a): write an abstraction relation for your implementation *)
  Definition atomic_pair_abstraction (ds : OneDiskAPI.State) (ps : AtomicPairAPI.State) : Prop :=
    (* SOL *)
    diskSize ds = 5 /\
    (diskGet ds ptr_a ?|= eq block0 ->
     diskGet ds data0a = Some (fst ps) /\
     diskGet ds data1a = Some (snd ps)) /\
    (forall b, diskGet ds ptr_a ?|= eq b ->
          b <> block0 ->
          diskGet ds data0b = Some (fst ps) /\
          diskGet ds data1b = Some (snd ps)).
  (* END *)
  (* STUB: True. *)

  (* EXERCISE (3a): come up with some examples of disks and pairs that satisfy
     the abstraction relation and those that don't. Prove them correct.

     Come up with at least 2 positive examples and 1 negative example. *)

  (* SOL *)
  Example abstraction_ok_ptr0 : forall b1 b2 b3 b4,
      atomic_pair_abstraction
        [block0; b1; b2; b3; b4] (b1, b2).
  Proof.
    unfold atomic_pair_abstraction; intuition auto.
  Qed.

  Example abstraction_ok_ptr1 : forall b1 b2 b3 b4,
      atomic_pair_abstraction
        [block1; b1; b2; b3; b4] (b3, b4).
  Proof.
    unfold atomic_pair_abstraction; simpl; intuition auto.
    exfalso; eauto.
    exfalso; eauto.
  Qed.

  Example abstraction_ok_ptr_same : forall b b1 b2,
      atomic_pair_abstraction
        [b; b1; b2; b1; b2] (b1, b2).
  Proof.
    unfold atomic_pair_abstraction; simpl; intuition auto.
  Qed.

  Example abstraction_nok_size : forall b1 b2,
      ~atomic_pair_abstraction [] (b1, b2).
  Proof.
    unfold atomic_pair_abstraction; simpl; intuition auto.
    omega.
  Qed.

  Example abstraction_nok_size2 : forall b1 b2,
      ~atomic_pair_abstraction [block0; block1] (b1, b2).
  Proof.
    unfold atomic_pair_abstraction; simpl; intuition auto.
    omega.
  Qed.

  Example abstraction_nok_size3 : forall b1 b2,
      ~atomic_pair_abstraction [block0; block1; block0; block1] (b1, b2).
  Proof.
    unfold atomic_pair_abstraction; simpl; intuition auto.
    omega.
  Qed.
  (* END *)

  Definition abstr : Abstraction AtomicPairAPI.State :=
    abstraction_compose d.abstr {| abstraction := atomic_pair_abstraction |}.

  (* For this lab, we provide a notation for diskUpd. Not only can you use this
     to write [diskUpd d a b] as [d [a |-> b]] but you will also see this notation
     in goals. This should especially make it easier to read goals with many
     updates of the same disk.

     Remember that the code still uses diskUpd underneath, so the same theorems
     apply. We recommend using [autorewrite with upd] or [autorewrite with upd
     in *] in this lab to simplify diskGet/diskUpd expressions, rather than
     using the theorems manually. *)
  Notation "d [ a |-> b ]" := (diskUpd d a b) (at level 8, left associativity).

  Opaque diskGet.

  (* EXERCISE (3b): prove your initialization procedure correct. *)
  Theorem init_ok : init_abstraction init recover abstr inited_any.
  Proof.
    eapply then_init_compose; eauto.
    (* SOL *)

    step_proc.
    destruct (r == 5).
    step_proc.
    step_proc.
    step_proc.
    step_proc.
    exists (block0, block0).
    unfold atomic_pair_abstraction.
    autorewrite with upd; intuition auto.

    step_proc.
  Qed.
  (* END *)
  (* STUB: Admitted. *)

  (* EXERCISE (3b): prove you can correctly get the pair using your abstraction
  relation. *)
  Theorem get_ok : proc_spec get_spec get recover abstr.
  Proof.
    unfold get.
    apply spec_abstraction_compose; simpl.
    (* SOL *)

    step_proc.
    destruct a'; simpl in *; intuition; subst; eauto.

    destruct (r == block0).
    step_proc; intuition; subst; eauto.
    step_proc; intuition; subst; eauto.
    step_proc; intuition; subst; eauto.
    unfold atomic_pair_abstraction in *; intuition.
    exists s.
    destruct s; intuition.
    replace (diskGet state data0a) in *.
    replace (diskGet state data1a) in *.
    simpl in *; subst; auto.

    step_proc; intuition; subst; eauto.
    step_proc; intuition; subst; eauto.
    step_proc; intuition; subst; eauto.

    unfold atomic_pair_abstraction in *; intuition.
    exists s.
    destruct s; intuition.
    specialize (H6 r); intuition.
    replace (diskGet state data0b) in *.
    replace (diskGet state data1b) in *.
    simpl in *; subst; auto.
  Qed.
  (* END *)
  (* STUB: Admitted. *)

  (* SOL *)
  Lemma abstraction_update_b : forall state p0 p,
      atomic_pair_abstraction state p0 ->
      diskGet state ptr_a ?|= eq block0 ->
      atomic_pair_abstraction
        (state [data0b |-> fst p] [data1b |-> snd p] [ptr_a |-> block1]) p.
  Proof.
    unfold atomic_pair_abstraction.
    intros.
    autorewrite with upd; intuition.
  Qed.

  Lemma abstraction_update_a : forall state p0 b p,
      atomic_pair_abstraction state p0 ->
      diskGet state ptr_a ?|= eq b ->
      b <> block0 ->
      atomic_pair_abstraction
        (state [data0a |-> fst p] [data1a |-> snd p] [ptr_a |-> block0]) p.
  Proof.
    unfold atomic_pair_abstraction.
    intros.
    autorewrite with upd; intuition.
  Qed.

  Hint Resolve
       abstraction_update_a
       abstraction_update_b.
  (* END *)

  Lemma diskGet_eq_values : forall d a b b',
      diskGet d a ?|= eq b ->
      diskGet d a ?|= eq b' ->
      a < diskSize d ->
      b = b'.
  Proof.
  (* SOL *)
    intros.
    destruct (diskGet d a) eqn:?; simpl in *.
    congruence.
    exfalso.
    apply disk_inbounds_not_none in Heqo; eauto.
  Qed.
  (* END *)
  (* STUB: Admitted. *)

  (* We used this tactic to simplify goals with
   H1: diskGet d a ?|= eq b
   H2: diskGet d a ?|= eq b'

   The tactic proves b = b'.
   *)
  Ltac eq_values :=
    match goal with
    | [ H: diskGet ?d ?a ?|= eq ?b,
           H': diskGet ?d ?a ?|= eq ?b' |- _ ] =>
      assert (b = b') by (apply (@diskGet_eq_values d a b b'); auto);
      subst
    end.

  (* SOL *)
  Lemma abstraction_partial_update_a : forall state p v v',
      atomic_pair_abstraction state p ->
      diskGet state ptr_a ?|= eq block0 ->
      atomic_pair_abstraction
        (state [data0b |-> v] [data1b |-> v']) p.
  Proof.
    unfold atomic_pair_abstraction.
    intros.
    autorewrite with upd; intuition;
      eq_values; exfalso; eauto.
  Qed.

  Lemma abstraction_partial_update1_a : forall state p v,
      atomic_pair_abstraction state p ->
      diskGet state ptr_a ?|= eq block0 ->
      atomic_pair_abstraction
        (state [data0b |-> v]) p.
  Proof.
    unfold atomic_pair_abstraction.
    intros.
    autorewrite with upd; intuition;
      eq_values; exfalso; eauto.
  Qed.

  Lemma abstraction_partial_update_b : forall state p b v v',
      atomic_pair_abstraction state p ->
      diskGet state ptr_a ?|= eq b ->
      b <> block0 ->
      atomic_pair_abstraction
        (state [data0a |-> v] [data1a |-> v']) p.
  Proof.
    unfold atomic_pair_abstraction.
    intros.
    autorewrite with upd; intuition;
      eq_values; exfalso; eauto.
  Qed.

  Lemma abstraction_partial_update1_b : forall state p b v,
      atomic_pair_abstraction state p ->
      diskGet state ptr_a ?|= eq b ->
      b <> block0 ->
      atomic_pair_abstraction
        (state [data0a |-> v]) p.
  Proof.
    unfold atomic_pair_abstraction.
    intros.
    autorewrite with upd; intuition;
      eq_values; exfalso; eauto.
  Qed.

  Hint Resolve
       abstraction_partial_update_a
       abstraction_partial_update_b
       abstraction_partial_update1_a
       abstraction_partial_update1_b.
  (* END *)

  (* EXERCISE (3c): prove that the atomic update is correct.

   We highly recommend separating at least the crash cases into lemmas and
   proving them separately. *)
  Theorem put_ok : forall v, proc_spec (put_spec v) (put v) recover abstr.
  Proof.
    unfold put; intros.
    apply spec_abstraction_compose; simpl.
    (* SOL *)

    step_proc.
    destruct a'; simpl in *; intuition; subst; eauto.
    destruct (r == block0).
    step_proc; intuition; subst; eauto.
    step_proc; intuition; subst; eauto.
    step_proc; intuition; subst; eauto.
    step_proc; intuition; subst; eauto.
    step_proc; intuition; subst; eauto.
    step_proc; intuition; subst; eauto.
    step_proc; intuition; subst; eauto.
    step_proc; intuition; subst; eauto.
  Qed.
  (* END *)
  (* STUB: Admitted. *)

  Theorem recover_noop : rec_noop recover abstr no_wipe.
  Proof.
    unfold rec_noop.
    intros.

    apply spec_abstraction_compose; simpl.
    step_proc; intros.
    eauto.

    destruct a; simpl in *.
    autounfold in *; intuition; subst; eauto.
  Qed.

End AtomicPair.
