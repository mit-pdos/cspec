Require Export RelationClasses.
Require Import Relation_Operators.
Require Import Ordering.
Require Import ProofIrrelevance.

Require Import String.
Require Import List.

(** * Decidable equality.

    [EqualDec] defines a notion of decidable equality for things
    of type [A].  This means that there is a function, called
    [equal_dec], which, given two things of type [A], will return
    whether they are equal or not.
  *)

Class EqualDec A :=
  equal_dec : forall x y : A, { x = y } + { x <> y }.

(**
    We define the notation [x == y] to mean our decidable equality
    between [x] and [y].
  *)

Notation " x == y " := (equal_dec (x :>) (y :>)) (no associativity, at level 70).

(**
    Here, we define some types for which we know how to compute
    decidable equality (namely, equality for [nat]s, and equality
    for [bool]s).
  *)

Instance nat_equal_dec : EqualDec nat := ltac:(hnf; decide equality).
Instance bool_equal_dec : EqualDec bool := ltac:(hnf; decide equality).

Instance string_equal_dec : EqualDec string := string_dec.
Instance list_equal_dec A `{dec:EqualDec A} : EqualDec (list A) := list_eq_dec dec.

Instance pair_equal_dec A B `{ea:EqualDec A} `{eb:EqualDec B} : EqualDec (A*B).
  intro; intros.
  destruct x; destruct y.
  destruct (a == a0); subst.
  destruct (b == b0); subst.
  all: intuition congruence.
Defined.


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
    inversion H; congruence.
Qed.

Ltac RelInstance_t :=
  intros;
  let refl := try solve [ hnf; intros; reflexivity ] in
  let symm := try solve [ hnf; intros; try symmetry; eauto ] in
  let trans := try solve [ hnf; intros; etransitivity; eauto ] in
  try match goal with
  | |- Reflexive _ =>
    hnf; intros; refl
  | |- Symmetric _ =>
    hnf; intros; symm
  | |- Transitive _ =>
    hnf; intros; trans
  | |- PreOrder _ =>
    constructor; hnf; intros; [ refl | trans ]
  | |- Equivalence _ =>
    constructor; hnf; intros; [ refl | symm | trans ]
  end.

Notation RelInstance := (ltac:(RelInstance_t)) (only parsing).
