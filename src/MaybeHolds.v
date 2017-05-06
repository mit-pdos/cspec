Set Implicit Arguments.

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
    (forall t, p t -> p' t) ->
    maybe_holds p mt ->
    maybe_holds p' mt.
Proof.
  unfold maybe_holds; destruct mt; eauto.
Qed.

Definition lift {T} (P:Prop) : T -> Prop := fun _ => P.

Corollary pred_false : forall T (p: T -> Prop) mt,
    maybe_holds (lift False) mt ->
    maybe_holds p mt.
Proof.
  unfold maybe_holds, lift; destruct mt; intros.
  contradiction.
  auto.
Qed.

Delimit Scope pred_scope with pred.

Notation "[| P |]" := (lift P) (at level 0) : pred_scope.
Notation "m |= F" := (maybe_holds F%pred m) (at level 20, F at level 50).
