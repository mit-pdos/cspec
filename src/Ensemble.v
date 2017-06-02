Require Import FunctionalExtensionality.
Require Import PropExtensionality.
Require Import RelationClasses.

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

  Definition Union A A' : Ensemble :=
    fromSet (fun y => In y A \/ In y A').

  Theorem Union_has_l : forall A A' x,
      In x A ->
      In x (Union A A').
  Proof.
    compute; auto.
  Qed.

  Theorem Union_has_r : forall A A' x,
      In x A' ->
      In x (Union A A').
  Proof.
    compute; auto.
  Qed.

  Theorem Union_inv : forall A A' x,
      In x (Union A A') ->
      In x A \/ In x A'.
  Proof.
    compute; auto.
  Qed.

  Definition contains A A' := forall x, In x A -> In x A'.

  Global Instance contains_preorder : PreOrder contains.
  Proof.
    firstorder.
  Defined.

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

  Ltac t := intros;
            repeat match goal with
                   | [ A: Ensemble |- _ ] => destruct A
                   end;
            compute in *;
            try solve [ intuition (subst; eauto) ].

  Lemma contains_Add : forall x A A',
      contains A A' ->
      In x A' ->
      contains (Add x A) A'.
  Proof.
    t.
  Qed.

  Lemma contains_Add_inv : forall x A A',
      contains (Add x A) A' ->
      contains A A' /\
      In x A'.
  Proof.
    t.
  Qed.

  Theorem Add_element : forall x A,
      In x A ->
      Add x A = A.
  Proof.
    intros.
    apply Ensemble_ext.
    t.
  Qed.

  Theorem contains_Singleton : forall x A,
      contains (Singleton x) A <->
      In x A.
  Proof.
    t.
  Qed.

  Theorem contains_Union_respectful : forall A0 A1 A0' A1',
      contains A0 A0' ->
      contains A1 A1' ->
      contains (Union A0 A1) (Union A0' A1').
  Proof.
    t.
  Qed.

  Theorem contains_Union_both : forall A A0 A1,
      contains A0 A ->
      contains A1 A ->
      contains (Union A0 A1) A.
  Proof.
    t.
  Qed.

  Theorem contains_Union_l : forall A A',
      contains A (Union A A').
  Proof.
    t.
  Qed.

  Theorem contains_Union_r : forall A A',
      contains A' (Union A A').
  Proof.
    t.
  Qed.

End Ensembles.

Arguments Ensemble U : clear implicits.

Hint Resolve Add_val Add_prev Singleton_has Union_has_l Union_has_r.

Hint Resolve -> contains_Singleton.
Hint Resolve <- contains_Singleton.

Hint Resolve contains_Union_both.

Notation "x ∈ A" := (In x A)
                      (at level 10, A at level 10,
                       no associativity,
                       only printing).
