Require Import Spec.Proc.
Require Import Spec.Exec.
Require Import Spec.Automation.
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

  Ltac exec_ind H :=
    let t ss ss' := (remember ss; remember ss') in
    match type of H with
    | exec _ ?ss ?ss' => t ss ss'
    | kleene_star _ ?ss ?ss' => t ss ss'
    end.

  Theorem exec_one : forall ts1 tid ts2 s1 tr1 s2 tr2,
      exec_at step tid (ts1, s1, tr1) (ts2, s2, tr2) ->
      forall ts3 s3 tr3, exec (ts2, s2, tr2) (ts3, s3, tr3) ->
                    exec (ts1, s1, tr1) (ts3, s3, tr3).
  Proof.
    intros.
    eapply star_one with (_,_,_).
    hnf; exists tid; eauto.
    eauto.
  Qed.

  Theorem exec_at_upd : forall tid ts p s tr mp' s' tr',
      exec_at step tid (ts [[tid := p]], s, tr) (thread_upd (ts [[tid :=p]]) tid mp', s', tr') ->
      exec_at step tid (ts [[tid := p]], s, tr) (thread_upd ts tid mp', s', tr').
  Proof.
    intros.
    autorewrite with t in *; auto.
  Qed.

  Lemma exec_prefix:
    forall tid s s' tr tr' s0 tr0 ts p p' ts1',
      kleene_star (exec_step step) (ts [[tid := p']], s0, tr0) (ts1', s', tr') ->
      kleene_star (proc_step step tid) (p, s, tr) (Ret, s0, tr0) ->
      exec (ts [[tid := p;; p']], s, tr) (ts1', s', tr').
  Proof.
    intros.
    etransitivity; eauto.
    clear H.
    exec_ind H0.
    generalize dependent s.
    generalize dependent tr.
    generalize dependent p.
    induct H0;
      repeat match goal with
             | [ H: (_, _) = (_, _) |- _ ] =>
               invert H; clear H
             end.
    reflexivity.
    inv_proc_step.
    simpl.
    eapply exec_one; eauto.
    apply exec_at_upd.
    eapply exec_proc; autorewrite with t; eauto using proc_step.
  Qed.

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
    generalize dependent s'.
    generalize dependent tr'.
    induct H.
    - repeat match goal with
             | [ H: (_, _) = (_, _) |- _ ] => invert H; clear H
             end.
      eexists; reflexivity.
    - exec_step_inv H.
      + invert H;
          cleanup_upd;
          try inv_proc_step.
        eauto using exec_prefix.
      + exists ts1'.
        (* TODO: why do we have an execution to ts0 [[tid := Atomic p ~ p']],
        but then another one from just ts0? what happened to knowing Atomic p ~
        p' is still there? *)
  Abort.

End Semantics.
