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

    destruct (r == block0).
    - step_prog; intros.
      exists tt; simpl; intuition idtac.

      step_prog; intros.
      exists tt; simpl; intuition idtac.

      step_prog; intros.
      eauto.

      simpl in *; intuition subst.
      2: unfold wipe in *; intuition.
      eexists. split; eauto. destruct s.

      invert_abstraction; intuition.
      rewrite H1 in *. rewrite H4 in *. simpl in *; congruence.
      rewrite H2 in *. simpl in *. pose block0_block1_differ. congruence.

    - step_prog; intros.
      exists tt; simpl; intuition idtac.

      step_prog; intros.
      exists tt; simpl; intuition idtac.

      step_prog; intros.
      eauto.

      simpl in *; intuition subst.
      2: unfold wipe in *; intuition.
      eexists. split; eauto. destruct s.

      invert_abstraction; intuition.
      rewrite H2 in *. simpl in *. pose block0_block1_differ. congruence.
      rewrite H1 in *. rewrite H4 in *. simpl in *; congruence.
  Qed.

  Theorem put_ok : forall v, prog_spec (put_spec v) (put v) recover abstr.
  Proof.
    unfold put.
    intros.

    apply spec_abstraction_compose; simpl.

    step_prog; intros.
    destruct a'; simpl in *; intuition idtac.
    exists tt; simpl; intuition idtac.

    destruct (r == block0).
    - step_prog; intros.
      exists tt; simpl; intuition idtac.

      step_prog; intros.
      exists tt; simpl; intuition idtac.

      step_prog; intros.
      exists tt; simpl; intuition idtac.

      step_prog; intros.
      eauto.

      simpl in *; intuition subst.
      2: unfold wipe in *; intuition.
      eexists. split; eauto.

      invert_abstraction; intuition.
      unfold atomic_pair_abstraction.
      autorewrite with upd.
      repeat ( ( rewrite diskUpd_eq by ( repeat rewrite diskUpd_size; omega ) ) ||
               rewrite diskUpd_neq by congruence ).
      intuition eauto.

      rewrite H2 in *. simpl in *. pose block0_block1_differ. congruence.

    - step_prog; intros.
      exists tt; simpl; intuition idtac.

      step_prog; intros.
      exists tt; simpl; intuition idtac.

      step_prog; intros.
      exists tt; simpl; intuition idtac.

      step_prog; intros.
      eauto.

      simpl in *; intuition subst.
      2: unfold wipe in *; intuition.
      eexists. split; eauto.

      invert_abstraction; intuition.
      rewrite H2 in *. simpl in *. pose block0_block1_differ. congruence.

      unfold atomic_pair_abstraction.
      autorewrite with upd.
      repeat ( ( rewrite diskUpd_eq by ( repeat rewrite diskUpd_size; omega ) ) ||
               rewrite diskUpd_neq by congruence ).
      intuition eauto.
  Qed.

  Theorem recover_noop : rec_noop recover abstr AtomicPairAPI.wipe.
  Proof.
    pocs_admit.
  Qed.

End AtomicPair.
