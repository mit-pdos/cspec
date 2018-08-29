Require Import Spec.Proc.
Require Import Spec.Exec.
Require Import Spec.ThreadsState.

Require Import Helpers.ProofAutomation.
Require Import Helpers.TransitionSystem.

Require Import List.
Import ListNotations.

Section Semantics.
  Variable Op:Type.
  Variable State:Type.
  Variable step: InstStep Op State.

  Notation exec := (exec step).

  Implicit Types (op:Op) (p: proc Op) (s:State) (tr:trace).

  Definition trace_incl p1 p2 :=
    forall ts tid,
    forall s s' tr tr' ts1',
      exec (ts [[tid := p1]], s, tr) (ts1', s', tr') ->
      exists ts2', exec (ts [[tid := p2]], s, tr) (ts2', s', tr').

  Ltac exec_step_inv H :=
    lazymatch type of H with
    | exec_step _ _ ?ss =>
      ((is_var ss; let ts := fresh "ts" in
                  let s := fresh "s" in
                  let tr := fresh "tr" in
                  destruct ss as ((ts & s) & tr)) || idtac);
      apply exec_step_inv in H;
      destruct H;
      propositional
    end.

  Theorem atomic_trace_incl : forall p p',
      trace_incl (Exec (Atomic p) p') (p;; p').
  Proof.
    unfold trace_incl; intros.
    match goal with
    | [ H: exec ?ss ?ss' |- _ ] =>
      remember ss as ss1;
        remember ss' as ss2
    end.
    generalize dependent ts.
    generalize dependent ts1'.
    induct H.
    - repeat match goal with
             | [ H: (_, _) = (_, _) |- _ ] => invert H; clear H
             end.
      eexists; reflexivity.
    - specialize (IHkleene_star _ eq_refl).
      exec_step_inv H.
      (* TODO: can construct executions for a whole list of actions *)
  Abort.

End Semantics.
