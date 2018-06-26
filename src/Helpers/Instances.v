Require Import RelationClasses.
Require Import Relation_Operators.
Require Import Ordering.
Require Import ProofIrrelevance.

Require Import Helpers.Helpers.

Local Hint Constructors clos_refl_trans_1n.
Instance clos_rt1n_pre A (R: A -> A -> Prop) : PreOrder (clos_refl_trans_1n A R).
Proof.
  constructor; hnf; eauto.
  induction 1; eauto.
Qed.

Instance comparison_eq_dec : EqualDec comparison.
hnf; decide equality.
Qed.

Instance ord_eq_dec A {o:Ordering A} : EqualDec A.
Proof.
  hnf; intros.
  destruct (cmp x y == Eq).
  apply cmp_eq in e; auto.
  right; intro; subst.
  rewrite cmp_refl in n; congruence.
Qed.

Instance sigT_eq_dec A (P: A -> Prop) (dec:EqualDec A) : EqualDec (sig P).
Proof.
  hnf; intros.
  destruct x as [x ?], y as [y ?].
  destruct (x == y); subst; [ left | right ].
  - f_equal.
    apply proof_irrelevance.
  - intro.
    invert H; congruence.
Qed.
