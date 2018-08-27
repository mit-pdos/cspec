Require Import Instances.

Set Implicit Arguments.

Definition Relation A := A -> A -> Prop.

Inductive kleene_star A (R: Relation A) : Relation A :=
| star_refl : forall x,
    kleene_star R x x
| star_one : forall x1 x2 x3,
    R x1 x2 ->
    kleene_star R x2 x3 ->
    kleene_star R x1 x3.

Instance kleene_star_PreOrder A (R: Relation A) : PreOrder (kleene_star R).
Proof.
  RelInstance_t.
  - constructor.
  - induction H; eauto using kleene_star.
Qed.

Instance kleene_star_one A (R:Relation A) : subrelation R (kleene_star R).
Proof.
  repeat (hnf; intros); eauto using kleene_star.
Qed.
