Require Import FunctionalExtensionality.
Require Import Helpers.Instances.

Set Implicit Arguments.


Section FunMap.

  Variable A : Type.
  Variable V : Type.
  Context {Aeq : EqualDec A}.

  Definition funmap := A -> V.

  Definition fupd (a : A) (v : V) (m : funmap) : funmap :=
    fun a' => if a == a' then v else m a'.

  Theorem fupd_eq : forall a v m,
    fupd a v m a = v.
  Proof.
    unfold fupd; intros.
    destruct (a == a); congruence.
  Qed.

  Theorem fupd_ne : forall a a' v m,
    a <> a' ->
    fupd a v m a' = m a'.
  Proof.
    unfold fupd; intros.
    destruct (a == a'); congruence.
  Qed.

  Theorem fupd_fupd_eq : forall a v v' m,
    fupd a v (fupd a v' m) = fupd a v m.
  Proof.
    unfold fupd; intros.
    eapply functional_extensionality; intros.
    destruct (a == x); congruence.
  Qed.

  Theorem fupd_fupd_ne : forall a v a' v' m,
    a <> a' ->
    fupd a v (fupd a' v' m) = fupd a' v' (fupd a v m).
  Proof.
    unfold fupd; intros.
    eapply functional_extensionality; intros.
    destruct (a == x); destruct (a' == x); congruence.
  Qed.

  Theorem fupd_same : forall a v m,
      m a = v ->
      fupd a v m = m.
  Proof.
    intros.
    extensionality a'; subst.
    destruct (a == a'); subst.
    rewrite fupd_eq; auto.
    rewrite fupd_ne; auto.
  Qed.

End FunMap.

Hint Rewrite fupd_eq : fupd.
Hint Rewrite fupd_ne using congruence : fupd.
Hint Rewrite fupd_fupd_eq using congruence : fupd.

Identity Coercion funmap_apply : funmap >-> Funclass.
