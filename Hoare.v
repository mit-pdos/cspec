(** Crash Hoare Logic specifications *)

(* TODO: document how specifications are structured *)

Require Import Automation.
Require Import Prog.
Require Import ProgTheorems.

Set Implicit Arguments.

Record Quadruple T :=
  Spec {
      pre: Prop;
      post: T -> PState -> Prop;
      crash: PState -> Prop;
    }.

(** A specification quantifies over ghost state of type A, and gives pre/post
conditions and crash invariant specialized to a particular initial state. (This
is why [pre] above is just a [Prop].) *)
Definition Specification A T := A -> PState -> Quadruple T.

Definition prog_spec T A (spec: Specification A T) (p: prog3 T) :=
  forall a pstate,
    pre (spec a pstate) ->
    forall r, exec p pstate r ->
         match r with
         | Finished v pstate' => post (spec a pstate) v pstate'
         | Crashed pstate' => crash (spec a pstate) pstate'
         | Failed => False
         end.

(** Hoare double higher-order precondition *)
Definition DoublePre T :=
  (* initial state *)
  PState ->
  (* postcondition *)
  (T -> PState -> Prop) ->
  (* crash invariant *)
  (PState -> Prop) ->
  Prop.

Definition prog_double T (pre: DoublePre T) (p: prog3 T) :=
  forall pstate postcond crashinv,
    pre pstate postcond crashinv ->
    forall r, exec p pstate r ->
         match r with
         | Finished v pstate' => postcond v pstate'
         | Crashed pstate' => crashinv pstate'
         | Failed => False
         end.

Definition prog_ok T A (spec: Specification A T) (p: prog3 T) :=
  forall T' (rx: T -> prog3 T'),
    prog_double
      (fun pstate postcond crashinv =>
         exists a, pre (spec a pstate) /\
              (forall r, prog_double
                      (fun pstate' postcond' crashinv' =>
                         post (spec a pstate) r pstate' /\
                         postcond' = postcond /\
                         crashinv' = crashinv)
                      (rx r)) /\
              (forall pstate', crash (spec a pstate) pstate' ->
                          crashinv pstate')) (Bind p rx).

Theorem prog_ok_to_spec : forall T A (spec: Specification A T) (p: prog3 T),
    (forall a pstate r pstate', pre (spec a pstate) ->
                           post (spec a pstate) r pstate' ->
                           crash (spec a pstate) pstate') ->
    prog_ok spec p -> prog_spec spec p.
Proof.
  unfold prog_ok, prog_double, prog_spec; intros.
  specialize (H0 _ Ret).
  specialize (H0 pstate).
  eapply H0.
  exists a; intuition eauto; subst.
  match goal with
  | [ H: exec (Ret _) _ _ |- _ ] =>
    apply exec_ret in H
  end.
  destruct r1; intuition (subst; eauto).
  apply monad_right_id; auto.
Qed.

Theorem prog_spec_to_ok : forall T A (spec: Specification A T) (p: prog3 T),
    (forall a pstate r pstate', pre (spec a pstate) ->
                           post (spec a pstate) r pstate' ->
                           crash (spec a pstate) pstate') ->
    prog_spec spec p -> prog_ok spec p.
Proof.
  unfold prog_ok, prog_double, prog_spec; intros.
  deex.
  match goal with
  | [ H: exec (Bind _ _) _ _ |- _ ] =>
    apply exec_bind in H
  end.
  intuition; repeat deex.
  + eapply H3; intuition eauto.
    eapply H0 in H2; eauto.
  + eapply H0 in H2; eauto.
  + subst.
    match goal with
    | [ Hexec: exec _ _ Failed |- _ ] =>
      eapply H0 in Hexec; eauto
    end.
Qed.

Remark crash_invariants_must_handle_pre :
  forall T A (spec: Specification A T) (p: prog3 T),
    prog_spec spec p ->
    forall a pstate, pre (spec a pstate) ->
                crash (spec a pstate) pstate.
Proof.
  unfold prog_spec; intros.
  specialize (H _ _ ltac:(eauto)).
  eapply (H (Crashed pstate)).
  apply can_crash_at_begin.
Qed.

Theorem double_weaken : forall T (pre pre': DoublePre T) (p: prog3 T),
    (forall pstate postcond crashinv, pre pstate postcond crashinv ->
                                 pre' pstate postcond crashinv) ->
    prog_double pre' p ->
    prog_double pre p.
Proof.
  unfold prog_double at 2; intros.
  eapply H0; eauto.
Qed.
