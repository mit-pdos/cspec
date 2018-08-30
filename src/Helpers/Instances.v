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

Ltac RelInstance_t :=
  intros;
  let refl := try solve [ hnf; intros; reflexivity ] in
  let symm := try solve [ hnf; intros; try symmetry; eauto ] in
  let trans := try solve [ hnf; intros; etransitivity; eauto ] in
  try match goal with
      | |- EqualDec _ =>
        hnf; decide equality
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

(**
    We define the notation [x == y] to mean our decidable equality
    between [x] and [y].
  *)

Notation " x == y " := (equal_dec x y) (no associativity, at level 70).

(* For units, an explicit definition has better computational behavior.
Specifically it is syntactically a [left], so any matches on [u == u']
automatically reduce to the true case; [decide equality] would first destruct
the arguments before producing [left]. *)
Instance unit_equal_dec : EqualDec unit :=
  fun x y => left (match x, y with
                | tt, tt => eq_refl
                end).

Instance nat_equal_dec : EqualDec nat := RelInstance.
Instance bool_equal_dec : EqualDec bool := RelInstance.

Instance string_equal_dec : EqualDec string := string_dec.
Instance list_equal_dec A `{dec:EqualDec A} : EqualDec (list A) := list_eq_dec dec.

Instance pair_equal_dec A B `{ea:EqualDec A} `{eb:EqualDec B} : EqualDec (A*B) :=
  RelInstance.

Instance option_equal_dec A `{ea:EqualDec A} : EqualDec (option A) := RelInstance.

Local Hint Constructors clos_refl_trans_1n.
Instance clos_rt1n_pre A (R: A -> A -> Prop) : PreOrder (clos_refl_trans_1n A R).
Proof.
  RelInstance_t.
  eauto.
  induction H; eauto.
Qed.

Instance comparison_eq_dec : EqualDec comparison := ltac:(hnf; decide equality).

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
