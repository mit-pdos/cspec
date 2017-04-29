(** Crash Hoare Logic specifications *)

(* TODO: document how specifications are structured *)

Require Import Automation.
Require Import Prog.
Require Import ProgTheorems.

Set Implicit Arguments.

Record Quadruple T State :=
  Spec {
      pre: Prop;
      post: T -> State -> Prop;
      crash: State -> Prop;
    }.

(** A specification quantifies over ghost state of type A, and gives pre/post
conditions and crash invariant specialized to a particular initial state. (This
is why [pre] above is just a [Prop].) *)
Definition Specification A T State := A -> State -> Quadruple T State.

Definition prog_spec A `(spec: Specification A T State) `(p: prog opT T)
           `(step: Semantics opT State) :=
  forall a state,
    pre (spec a state) ->
    forall r, exec step p state r ->
         match r with
         | Finished v state' => post (spec a state) v state'
         | Crashed state' => crash (spec a state) state'
         end.

(** Hoare double higher-order precondition *)
Definition DoublePre T State :=
  (* initial state *)
  State ->
  (* postcondition *)
  (T -> State -> Prop) ->
  (* crash invariant *)
  (State -> Prop) ->
  Prop.

Definition prog_double `(pre: DoublePre T State) `(p: prog opT T)
           `(step: Semantics opT State) :=
  forall state postcond crashinv,
    pre state postcond crashinv ->
    forall r, exec step p state r ->
         match r with
         | Finished v state' => postcond v state'
         | Crashed state' => crashinv state'
         end.

Definition prog_ok A `(spec: Specification A T State) `(p: prog opT T)
           `(step: Semantics opT State) :=
  forall T' (rx: T -> prog opT T'),
    prog_double
      (fun state postcond crashinv =>
         exists a, pre (spec a state) /\
              (forall r, prog_double
                      (fun state' postcond' crashinv' =>
                         post (spec a state) r state' /\
                         postcond' = postcond /\
                         crashinv' = crashinv)
                      (rx r) step) /\
              (forall state', crash (spec a state) state' ->
                     crashinv state')) (Bind p rx) step.

Theorem prog_ok_to_spec : forall `(step: Semantics opT State)
                            A `(spec: Specification A T State) (p: prog opT T),
    (forall a state r state', pre (spec a state) ->
                 post (spec a state) r state' ->
                 crash (spec a state) state') ->
    prog_ok spec p step -> prog_spec spec p step.
Proof.
  unfold prog_ok, prog_double, prog_spec; intros.
  specialize (H0 _ Ret).
  specialize (H0 state).
  eapply H0.
  exists a; intuition eauto; subst.
  match goal with
  | [ H: exec _ (Ret _) _ _ |- _ ] =>
    apply exec_ret in H
  end.
  destruct r1; intuition (subst; eauto).
  apply monad_right_id; auto.
Qed.

Theorem prog_spec_to_ok : forall `(step: Semantics opT State)
                            A `(spec: Specification A T State) (p: prog opT T),
    prog_spec spec p step -> prog_ok spec p step.
Proof.
  unfold prog_ok, prog_double, prog_spec; intros.
  deex.
  match goal with
  | [ H: exec _ (Bind _ _) _ _ |- _ ] =>
    apply exec_bind in H
  end.
  intuition; repeat deex.
  + eapply H2; intuition eauto.
    eapply H in H1; eauto.
  + eapply H in H1; eauto.
Qed.

Remark crash_invariants_must_handle_pre :
  forall `(step: Semantics opT State)
    A `(spec: Specification A T State) (p: prog opT T),
    prog_spec spec p step ->
    forall a state, pre (spec a state) ->
           crash (spec a state) state.
Proof.
  unfold prog_spec; intros.
  specialize (H _ _ ltac:(eauto)).
  eapply (H (Crashed state)).
  apply can_crash_at_begin.
Qed.

Theorem double_weaken : forall `(step: Semantics opT State)
                          T (pre pre': DoublePre T State) (p: prog opT T),
    (forall state postcond crashinv, pre state postcond crashinv ->
                            pre' state postcond crashinv) ->
    prog_double pre' p step ->
    prog_double pre p step.
Proof.
  unfold prog_double at 2; intros.
  eapply H0; eauto.
Qed.
