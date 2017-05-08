Set Implicit Arguments.

(** Definition of [maybe_holds], stating a predicate holds over an optional
value if the value is present.

    To reflect the expected usage of this primitive, we also define two notations:
    - [mv |= p] states that p holds on mv, if mv is present (the notation
    desugars to [maybe_holds p mv])
    - to state that an optional value is definitely missing, we provide a
      predicate [missing], so that [mv |= missing] implies that mv is None.
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

Definition missing {T} : T -> Prop := fun _ => False.

Corollary pred_missing : forall T (p: T -> Prop) mt,
    maybe_holds missing mt ->
    maybe_holds p mt.
Proof.
  unfold missing; intros.
  eapply pred_weaken; eauto.
  contradiction.
Qed.

Delimit Scope pred_scope with pred.

Notation "m |= F" := (maybe_holds F%pred m) (at level 20, F at level 50).
