Require Import Arith.
Require Import Bool.
Require Import List.

Set Implicit Arguments.


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

Instance nat_equal_dec : EqualDec nat := eq_nat_dec.
Instance bool_equal_dec : EqualDec bool := bool_dec.


(** * [maybe_holds] predicate.

    One pattern that shows up in our lab assignments is that we
    want to say something about an optional value.  That is, we
    have something of type [option T], which is either [Some x]
    where [x] is of type [T], or is [None].  We want to make
    staements of the form ``if it's [Some x], then something is
    true about [x]''.  This shows up when we talk about a disk
    that might or might not have failed, or when we talk about
    the contents of a disk block that might or might not be there
    (e.g., because it's out of bounds).

    We define [maybe_holds] to formalize this notion.  [maybe_holds]
    takes a predicate, [T -> Prop], and an [option T].
  *)

Definition maybe_holds T (p:T -> Prop) : option T -> Prop :=
  fun mt => match mt with
         | Some t => p t
         | None => True
         end.

Theorem holds_in_none_eq : forall T (p:T -> Prop) mt,
    mt = None ->
    maybe_holds p mt.
Proof.
  intros; subst.
  simpl; auto.
Qed.

Theorem holds_in_some : forall T (p:T -> Prop) (v:T),
    p v ->
    maybe_holds p (Some v).
Proof.
  simpl; auto.
Qed.

Theorem holds_in_some_eq : forall T (p:T -> Prop) (v:T) mt,
    mt = Some v ->
    p v ->
    maybe_holds p mt.
Proof.
  intros; subst.
  simpl; auto.
Qed.

Theorem holds_some_inv_eq : forall T (p: T -> Prop) mt v,
    mt = Some v ->
    maybe_holds p mt ->
    p v.
Proof.
  intros; subst.
  auto.
Qed.

Theorem pred_weaken : forall T (p p': T -> Prop) mt,
    maybe_holds p mt ->
    (forall t, p t -> p' t) ->
    maybe_holds p' mt.
Proof.
  unfold maybe_holds; destruct mt; eauto.
Qed.

(** To reflect the expected usage of this primitive, we define
    two notations:

    - [mv ?|= p] states that [p] holds on [mv], if [mv] is present.
      This notation simply translates to [maybe_holds p mv].

    - To state that an optional value is definitely missing,
      we provide a predicate [missing], so that [mv ?|= missing]
      implies that [mv] is [None].  The [missing] predicate is simply
      [False], which allows us to conclude by contradiction that
      there's no way the optional value could be [Some x].
  *)

Notation "m ?|= F" := (maybe_holds F m) (at level 20, F at level 50).

Definition missing {T} : T -> Prop := fun _ => False.

Theorem pred_missing : forall T (p: T -> Prop) mt,
    mt ?|= missing ->
    mt ?|= p.
Proof.
  unfold missing; intros.
  eapply pred_weaken; eauto.
  contradiction.
Qed.
