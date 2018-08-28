Require Import Instances.

Set Implicit Arguments.

Generalizable Variable R.

Section TransitionSystem.
  Variable A:Type.

  Definition Relation := A -> A -> Prop.
  Implicit Types (R:Relation).

  Inductive kleene_star R : Relation :=
  | star_refl : forall x,
      kleene_star R x x
  | star_one : forall x1 x2 x3,
      R x1 x2 ->
      kleene_star R x2 x3 ->
      kleene_star R x1 x3.

  Global Instance kleene_star_PreOrder : PreOrder (kleene_star R).
  Proof.
    RelInstance_t.
    - constructor.
    - induction H; eauto using kleene_star.
  Qed.

  Theorem kleene_star_one : forall R x1 x2, R x1 x2 -> kleene_star R x1 x2.
  Proof.
    eauto using kleene_star.
  Qed.

  Global Instance kleene_star_sub : subrelation R (kleene_star R) :=
    kleene_star_one.

  Definition invariant (I: A -> Prop) R :=
    forall x1, I x1 ->
          forall x2, R x1 x2 -> I x2.

  Theorem invariant_star : forall I R,
      invariant I R ->
      invariant I (kleene_star R).
  Proof.
    unfold invariant; intros.
    induction H1; eauto.
  Qed.

  Theorem invariant_star' : forall I R,
      invariant I (kleene_star R) ->
      invariant I R.
  Proof.
    unfold invariant; intros.
    eapply H; eauto using kleene_star_one.
  Qed.

End TransitionSystem.
