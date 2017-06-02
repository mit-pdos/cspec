Require Import FunctionalExtensionality.
Require Import PropExtensionality.

Section Ensembles.

  Context {U:Type}.

  Implicit Types (x y:U).

  Definition Ensemble := U -> Prop.

  Implicit Type (A:Ensemble).

  Inductive add A x : Ensemble :=
  | add_new: add A x x
  | add_prev: forall y, A y -> add A x y.

  Inductive Singleton x : Ensemble :=
  | in_singleton: Singleton x x.

  Definition In x A : Prop := A x.

  Definition contains A A' := forall x, A x -> A' x.
  Definition same_set A A' := forall x, A x <-> A' x.

  Theorem Ensemble_ext : forall A A', same_set A A' -> A = A'.
  Proof.
    unfold same_set; intros.
    extensionality x.
    apply propositional_extensionality.
    auto.
  Qed.

End Ensembles.

Arguments Ensemble U : clear implicits.

Hint Constructors add.
Hint Constructors Singleton.
