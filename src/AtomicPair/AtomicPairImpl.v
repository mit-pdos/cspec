Require Import POCS.
Require Import AtomicPair.AtomicPairAPI.
Require Import OneDisk.OneDiskAPI.


Module AtomicPair (d : OneDiskAPI) <: AtomicPairAPI.

  Definition get : prog (block*block) :=
    ptr <- d.read 0;
    if ptr == block0 then
      a <- d.read 1;
      b <- d.read 2;
      Ret (a, b)
    else
      a <- d.read 3;
      b <- d.read 4;
      Ret (a, b).

  Definition put (p : block*block) : prog unit :=
    ptr <- d.read 0;
    if ptr == block0 then
      _ <- d.write 3 (fst p);
      _ <- d.write 4 (snd p);
      _ <- d.write 0 block1;
      Ret tt
    else
      _ <- d.write 1 (fst p);
      _ <- d.write 2 (snd p);
      _ <- d.write 0 block0;
      Ret tt.

  Definition init : prog InitResult :=
    len <- d.diskSize;
    if len == 5 then
      _ <- d.write 0 block0;
      Ret Initialized
    else
      Ret InitFailed.

  Definition recover : prog unit :=
    d.recover.


  Definition atomic_pair_abstraction (ds : OneDiskAPI.State) (ps : AtomicPairAPI.State) : Prop :=
    size ds = 5 /\
    (ds 0 = Some block0 /\ ds 1 = Some (fst ps) /\ ds 2 = Some (snd ps) \/
     ds 0 = Some block1 /\ ds 3 = Some (fst ps) /\ ds 4 = Some (snd ps)).

  Definition abstr : Abstraction AtomicPairAPI.State :=
    abstraction_compose d.abstr {| abstraction := atomic_pair_abstraction |}.

  Ltac invert_abstraction :=
    match goal with
    | H : atomic_pair_abstraction _ _ |- _ => inversion H; clear H; subst_var; simpl in *
    end.


  Theorem get_ok : prog_spec get_spec get recover abstr.
  Proof.
    unfold get.
    intros.

    apply spec_abstraction_compose; simpl.

    step_prog; intros.
    destruct a'; simpl in *; intuition idtac.
    exists tt; simpl; intuition idtac.
    2: unfold wipe in *; simpl in *; intuition subst; eauto.

    destruct (r == block0).
    - step_prog; intros.
      exists tt; simpl; intuition idtac.
      2: unfold wipe in *; simpl in *; intuition subst; eauto.

      step_prog; intros.
      exists tt; simpl; intuition idtac.
      2: unfold wipe in *; simpl in *; intuition subst; eauto.

      step_prog; intros.
      eauto.

      simpl in *; intuition subst.
      2: unfold wipe in *; simpl in *; intuition subst; eauto.
      eexists. split; eauto. destruct s.

      invert_abstraction; intuition.
      rewrite H1 in *. rewrite H4 in *. simpl in *; congruence.
      rewrite H2 in *. simpl in *. pose block0_block1_differ. congruence.

    - step_prog; intros.
      exists tt; simpl; intuition idtac.
      2: unfold wipe in *; simpl in *; intuition subst; eauto.

      step_prog; intros.
      exists tt; simpl; intuition idtac.
      2: unfold wipe in *; simpl in *; intuition subst; eauto.

      step_prog; intros.
      eauto.

      simpl in *; intuition subst.
      2: unfold wipe in *; simpl in *; intuition subst; eauto.
      eexists. split; eauto. destruct s.

      invert_abstraction; intuition.
      rewrite H2 in *. simpl in *. pose block0_block1_differ. congruence.
      rewrite H1 in *. rewrite H4 in *. simpl in *; congruence.
  Qed.


  Lemma atomic_pair_abstraction_diskUpd12 : forall state s a v,
    (a = 1 \/ a = 2) ->
    atomic_pair_abstraction state s ->
    state 0 ?|= eq block1 ->
    atomic_pair_abstraction (diskUpd state a v) s.
  Proof.
    unfold atomic_pair_abstraction; intros.
    repeat rewrite diskUpd_neq by ((intuition congruence) || (intuition omega)).
    repeat rewrite diskUpd_eq by ( intuition omega ).
    repeat rewrite diskUpd_neq by congruence.
    autorewrite with upd.
    pose block0_block1_differ.
    intuition auto.
    rewrite H3 in *; congruence.
    2: rewrite H3 in *; congruence.
    right. repeat rewrite diskUpd_neq by omega. auto.
    right. repeat rewrite diskUpd_neq by omega. auto.
  Qed.

  Lemma atomic_pair_abstraction_diskUpd34 : forall state s a v,
    (a = 3 \/ a = 4) ->
    atomic_pair_abstraction state s ->
    state 0 ?|= eq block0 ->
    atomic_pair_abstraction (diskUpd state a v) s.
  Proof.
    unfold atomic_pair_abstraction; intros.
    autorewrite with upd.
    intuition auto;
      repeat rewrite diskUpd_neq by congruence.
    intuition auto.
    pose block0_block1_differ.
    rewrite H3 in *; congruence.
    intuition auto.
    pose block0_block1_differ.
    rewrite H3 in *; congruence.
  Qed.

  Lemma atomic_pair_abstraction_state0 : forall (state : State) F a v,
    a <> 0 ->
    state 0 ?|= F ->
    (diskUpd state a v) 0 ?|= F.
  Proof.
    intros.
    rewrite diskUpd_neq; auto.
  Qed.

  Lemma atomic_pair_abstraction_diskUpd340 : forall state v0 v,
    atomic_pair_abstraction state v0 ->
    atomic_pair_abstraction
      (diskUpd (diskUpd (diskUpd state 3 (fst v)) 4 (snd v)) 0 block1) v.
  Proof.
    unfold atomic_pair_abstraction; intros.
    autorewrite with upd.
    repeat ( (rewrite diskUpd_eq by (autorewrite with upd; omega)) ||
             (rewrite diskUpd_neq by (autorewrite with upd; omega)) ).
    intuition auto.
  Qed.

  Lemma atomic_pair_abstraction_diskUpd120 : forall state v0 v,
    atomic_pair_abstraction state v0 ->
    atomic_pair_abstraction
      (diskUpd (diskUpd (diskUpd state 1 (fst v)) 2 (snd v)) 0 block0) v.
  Proof.
    unfold atomic_pair_abstraction; intros.
    autorewrite with upd.
    repeat ( (rewrite diskUpd_eq by (autorewrite with upd; omega)) ||
             (rewrite diskUpd_neq by (autorewrite with upd; omega)) ).
    intuition auto.
  Qed.

  Hint Resolve atomic_pair_abstraction_diskUpd12.
  Hint Resolve atomic_pair_abstraction_diskUpd34.
  Hint Resolve atomic_pair_abstraction_state0.
  Hint Resolve atomic_pair_abstraction_diskUpd340.
  Hint Resolve atomic_pair_abstraction_diskUpd120.

  Theorem put_ok : forall v, prog_spec (put_spec v) (put v) recover abstr.
  Proof.
    unfold put.
    intros.

    apply spec_abstraction_compose; simpl.

    step_prog; intros.
    destruct a'; simpl in *; intuition idtac.
    exists tt; simpl; intuition.
    2: unfold wipe in *; simpl in *; intuition subst; eauto 10.

    destruct (r == block0).
    - step_prog; intros.
      exists tt; simpl; intuition idtac.
      2: unfold wipe in *; simpl in *; intuition subst; eauto 10.
      2: unfold wipe in *; simpl in *; intuition subst; eauto 10.

      step_prog; intros.
      exists tt; simpl; intuition idtac.
      2: unfold wipe in *; simpl in *; intuition subst; eauto 10.
      2: unfold wipe in *; simpl in *; intuition subst; eauto 10.

      step_prog; intros.
      exists tt; simpl; intuition idtac.
      2: unfold wipe in *; simpl in *; intuition subst; eauto 10.
      2: unfold wipe in *; simpl in *; intuition subst; eauto 10.

      step_prog; intros.
      eauto.

      simpl in *; intuition subst.
      unfold wipe in *; simpl in *; intuition subst; eauto 10.
      unfold wipe in *; simpl in *; intuition subst; eauto 10.

    - step_prog; intros.
      exists tt; simpl; intuition idtac.
      2: unfold wipe in *; simpl in *; intuition subst; eauto 10.
      2: unfold wipe in *; simpl in *; intuition subst; eauto 10.

      2: assert (r = block1); subst.
      2: pose block0_block1_differ.
      2: unfold atomic_pair_abstraction in *; simpl in *; intuition auto.
      2: rewrite H2 in *; simpl in *; subst; congruence.
      2: rewrite H2 in *; simpl in *; subst; congruence.
      2: unfold wipe in *; simpl in *; intuition subst; eauto 10.

      assert (r = block1); subst.
      pose block0_block1_differ.
      unfold atomic_pair_abstraction in *; simpl in *; intuition auto.
      rewrite H3 in *; simpl in *; subst; congruence.
      rewrite H3 in *; simpl in *; subst; congruence.

      step_prog; intros.
      exists tt; simpl; intuition idtac.
      2: unfold wipe in *; simpl in *; intuition subst; eauto 10.
      2: unfold wipe in *; simpl in *; intuition subst; eauto 10.

      step_prog; intros.
      exists tt; simpl; intuition idtac.
      2: unfold wipe in *; simpl in *; intuition subst; eauto 10.
      2: unfold wipe in *; simpl in *; intuition subst; eauto 10.

      step_prog; intros.
      eauto.

      simpl in *; intuition subst.
      unfold wipe in *; simpl in *; intuition subst; eauto 10.
      unfold wipe in *; simpl in *; intuition subst; eauto 10.
  Qed.

  Theorem recover_noop : rec_noop recover abstr AtomicPairAPI.wipe.
  Proof.
    pocs_admit.
  Qed.

End AtomicPair.
