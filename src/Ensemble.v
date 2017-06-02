Require Import FunctionalExtensionality.
Require Import PropExtensionality.

Section Ensembles.

  Context {U:Type}.

  Implicit Types (x y:U).

  Record Ensemble :=
    fromSet { Contains: U -> Prop }.

  Implicit Type (A:Ensemble).

  Definition In x A := Contains A x.

  Definition Add x A : Ensemble :=
    fromSet (fun y => y = x \/ In y A).

  Theorem Add_val : forall x y A,
      y = x ->
      In y (Add x A).
  Proof.
    destruct A; simpl; eauto.
  Qed.

  Theorem Add_prev : forall x y A,
      In y A ->
      In y (Add x A).
  Proof.
    destruct A; simpl; eauto.
  Qed.

  Theorem Add_inv : forall A x y,
      In y (Add x A) ->
      y = x \/ In y A.
  Proof.
    destruct A; simpl; intuition.
  Qed.

  Definition Singleton x : Ensemble :=
    fromSet (fun y => y = x).

  Theorem Singleton_has : forall x y,
      y = x ->
      In y (Singleton x).
  Proof.
    compute; auto.
  Qed.

  Theorem Singleton_inv : forall x y,
      In y (Singleton x) ->
      y = x.
  Proof.
    compute; auto.
  Qed.

  Definition contains A A' := forall x, In x A -> In x A'.
  Definition same_set A A' := forall x, In x A <-> In x A'.

  Theorem Ensemble_ext : forall A A', same_set A A' -> A = A'.
  Proof.
    unfold same_set; intros.
    destruct A, A'; simpl in *.
    f_equal.
    extensionality x.
    apply propositional_extensionality.
    auto.
  Qed.

End Ensembles.

Arguments Ensemble U : clear implicits.

Hint Resolve Add_val Add_prev Singleton_has.

Notation "x ∈ A" := (In x A)
                      (at level 10, A at level 10,
                       no associativity,
                       only printing).
