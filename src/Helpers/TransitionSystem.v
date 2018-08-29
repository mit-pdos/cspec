Require Import Helpers.Instances.
Require Import Helpers.ProofAutomation.

Require Import Morphisms.

Set Implicit Arguments.

Generalizable Variable R.

Section TransitionSystem.
  Variable A:Type.

  Definition Relation := A -> A -> Prop.
  Implicit Types (R:Relation).

  Definition rimpl R1 R2 := forall x y, R1 x y -> R2 x y.
  Definition riff R1 R2 := rimpl R1 R2 /\ rimpl R2 R1.

  Infix "--->" := rimpl (at level 14, no associativity).
  Infix "<--->" := riff (at level 14, no associativity).

  Global Instance rimpl_PreOrder : PreOrder rimpl.
  Proof.
    firstorder.
  Qed.

  Global Instance riff_Equivalence : Equivalence riff.
  Proof.
    firstorder.
  Qed.

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

  Theorem kleene_star_one : forall R, R ---> kleene_star R.
  Proof.
    unfold rimpl.
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
    eapply H; eauto.
    eapply kleene_star_one; eauto.
  Qed.

  Definition rel_app R1 R2 : Relation :=
    fun x z => exists y, R1 x y /\ R2 y z.

  Infix ">>" := rel_app (at level 12, left associativity).

  Theorem rel_app_assoc : forall R1 R2 R3,
      R1 >> R2 >> R3 <---> R1 >> (R2 >> R3).
  Proof.
    firstorder.
  Qed.

  Global Instance rel_app_impl :
    Proper (rimpl ==> rimpl ==> rimpl) rel_app.
  Proof.
    firstorder.
  Qed.

  Global Instance rel_app_iff :
    Proper (riff ==> riff ==> riff) rel_app.
  Proof.
    firstorder.
  Qed.

  Theorem kleene_star_duplicate : forall R,
      kleene_star R >> kleene_star R <---> kleene_star R.
  Proof.
    unfold rel_app, riff, rimpl; split; propositional.
    - etransitivity; eauto.
    - exists x; split; eauto.
      reflexivity.
  Qed.

End TransitionSystem.
