Require Import POCS.
Require Import AtomicPairAPI.
Require Import Common.OneDiskAPI.


Module AtomicPair (d : OneDiskAPI) <: AtomicPairAPI.

  Definition get : proc (block*block) :=
    ptr <- d.read 0;
    if ptr == block0 then
      a <- d.read 1;
      b <- d.read 2;
      Ret (a, b)
    else
      a <- d.read 3;
      b <- d.read 4;
      Ret (a, b).

  Definition put (p : block*block) : proc unit :=
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

  Definition init' : proc InitResult :=
    len <- d.size;
    if len == 5 then
      _ <- d.write 0 block0;
      Ret Initialized
    else
      Ret InitFailed.

  Definition init := then_init d.init init'.

  Definition recover: proc unit :=
    d.recover.


  Definition atomic_pair_abstraction (ds : OneDiskAPI.State) (ps : AtomicPairAPI.State) : Prop :=
    diskSize ds = 5 /\
    (diskGet ds 0 = Some block0 /\ diskGet ds 1 = Some (fst ps) /\ diskGet ds 2 = Some (snd ps) \/
     diskGet ds 0 = Some block1 /\ diskGet ds 3 = Some (fst ps) /\ diskGet ds 4 = Some (snd ps)).

  Definition abstr : Abstraction AtomicPairAPI.State :=
    abstraction_compose d.abstr {| abstraction := atomic_pair_abstraction |}.

  Ltac invert_abstraction :=
    match goal with
    | H : atomic_pair_abstraction _ _ |- _ => inversion H; clear H; subst_var; simpl in *
    end.


  Theorem init_ok : init_abstraction init recover abstr inited_any.
  Proof.
    eapply then_init_compose; eauto.

    step_prog; intros.
    exists tt; simpl; intuition idtac.

    destruct (r == 5).
    - step_prog; intros.
      exists tt; simpl; intuition idtac.

      step_prog; intros.
      eauto.

      simpl in *; intuition subst.
      edestruct disk_inbounds_exists with (d := state) (a := 1); try omega.
      edestruct disk_inbounds_exists with (d := state) (a := 2); try omega.

      unfold atomic_pair_abstraction; exists (x, x0).
      autorewrite with upd.
      repeat rewrite diskUpd_eq by omega.
      repeat rewrite diskUpd_neq by omega.
      intuition auto.

    - step_prog; intros.
      eauto.

      simpl in *; intuition subst.
  Qed.

  Theorem get_ok : proc_spec get_spec get recover abstr.
  Proof.
    unfold get.
    intros.

    apply spec_abstraction_compose; simpl.

    step_prog; intros.
    destruct a'; simpl in *; intuition idtac.
    exists tt; simpl; intuition idtac.
    2: autounfold in *; simpl in *; intuition subst; eauto.

    destruct (r == block0).
    - step_prog; intros.
      exists tt; simpl; intuition idtac.
      2: autounfold in *; simpl in *; intuition subst; eauto.

      step_prog; intros.
      exists tt; simpl; intuition idtac.
      2: autounfold in *; simpl in *; intuition subst; eauto.

      step_prog; intros.
      eauto.

      simpl in *; intuition subst.
      2: autounfold in *; simpl in *; intuition subst; eauto.
      eexists. split; eauto. destruct s.

      invert_abstraction; intuition.
      rewrite H1 in *. rewrite H4 in *. simpl in *; congruence.
      rewrite H2 in *. simpl in *. pose block0_block1_differ. congruence.

    - step_prog; intros.
      exists tt; simpl; intuition idtac.
      2: autounfold in *; simpl in *; intuition subst; eauto.

      step_prog; intros.
      exists tt; simpl; intuition idtac.
      2: autounfold in *; simpl in *; intuition subst; eauto.

      step_prog; intros.
      eauto.

      simpl in *; intuition subst.
      2: autounfold in *; simpl in *; intuition subst; eauto.
      eexists. split; eauto. destruct s.

      invert_abstraction; intuition.
      rewrite H2 in *. simpl in *. pose block0_block1_differ. congruence.
      rewrite H1 in *. rewrite H4 in *. simpl in *; congruence.
  Qed.


  Theorem atomic_pair_abstraction_diskUpd12 : forall state s a v,
    (a = 1 \/ a = 2) ->
    atomic_pair_abstraction state s ->
    diskGet state 0 ?|= eq block1 ->
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

  Theorem atomic_pair_abstraction_diskUpd34 : forall state s a v,
    (a = 3 \/ a = 4) ->
    atomic_pair_abstraction state s ->
    diskGet state 0 ?|= eq block0 ->
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

  Theorem atomic_pair_abstraction_state0 : forall (state : State) F a v,
    a <> 0 ->
    diskGet state 0 ?|= F ->
    diskGet (diskUpd state a v) 0 ?|= F.
  Proof.
    intros.
    rewrite diskUpd_neq; auto.
  Qed.

  Theorem atomic_pair_abstraction_diskUpd340 : forall state v0 v,
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

  Theorem atomic_pair_abstraction_diskUpd120 : forall state v0 v,
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

  Theorem put_ok : forall v, proc_spec (put_spec v) (put v) recover abstr.
  Proof.
    unfold put.
    intros.

    apply spec_abstraction_compose; simpl.

    step_prog; intros.
    destruct a'; simpl in *; intuition idtac.
    exists tt; simpl; intuition.
    2: autounfold in *; simpl in *; intuition subst; eauto 10.

    destruct (r == block0).
    - step_prog; intros.
      exists tt; simpl; intuition idtac.
      2: autounfold in *; simpl in *; intuition subst; eauto 10.
      2: autounfold in *; simpl in *; intuition subst; eauto 10.

      step_prog; intros.
      exists tt; simpl; intuition idtac.
      2: autounfold in *; simpl in *; intuition subst; eauto 10.
      2: autounfold in *; simpl in *; intuition subst; eauto 10.

      step_prog; intros.
      exists tt; simpl; intuition idtac.
      2: autounfold in *; simpl in *; intuition subst; eauto 10.
      2: autounfold in *; simpl in *; intuition subst; eauto 10.

      step_prog; intros.
      eauto.

      simpl in *; intuition subst.
      autounfold in *; simpl in *; intuition subst; eauto 10.
      autounfold in *; simpl in *; intuition subst; eauto 10.

    - step_prog; intros.
      exists tt; simpl; intuition idtac.
      2: autounfold in *; simpl in *; intuition subst; eauto 10.
      2: autounfold in *; simpl in *; intuition subst; eauto 10.

      2: assert (r = block1); subst.
      2: pose block0_block1_differ.
      2: unfold atomic_pair_abstraction in *; simpl in *; intuition auto.
      2: rewrite H2 in *; simpl in *; subst; congruence.
      2: rewrite H2 in *; simpl in *; subst; congruence.
      2: autounfold in *; simpl in *; intuition subst; eauto 10.

      assert (r = block1); subst.
      pose block0_block1_differ.
      unfold atomic_pair_abstraction in *; simpl in *; intuition auto.
      rewrite H3 in *; simpl in *; subst; congruence.
      rewrite H3 in *; simpl in *; subst; congruence.

      step_prog; intros.
      exists tt; simpl; intuition idtac.
      2: autounfold in *; simpl in *; intuition subst; eauto 10.
      2: autounfold in *; simpl in *; intuition subst; eauto 10.

      step_prog; intros.
      exists tt; simpl; intuition idtac.
      2: autounfold in *; simpl in *; intuition subst; eauto 10.
      2: autounfold in *; simpl in *; intuition subst; eauto 10.

      step_prog; intros.
      eauto.

      simpl in *; intuition subst.
      autounfold in *; simpl in *; intuition subst; eauto 10.
      autounfold in *; simpl in *; intuition subst; eauto 10.
  Qed.

  Theorem recover_noop : rec_noop recover abstr no_wipe.
  Proof.
    unfold rec_noop.
    intros.

    apply spec_abstraction_compose; simpl.
    step_prog; intros.
    eauto.

    destruct a; simpl in *.
    autounfold in *; intuition eauto.
    subst; eauto.
  Qed.

End AtomicPair.
