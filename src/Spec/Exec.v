Require Import Spec.Proc.
Require Import Spec.ThreadsState.
Require Import Spec.Automation.

Require Import Helpers.TransitionSystem.
Require Import Helpers.ProofAutomation.
Require Import Helpers.RecordSet.
Require Import Helpers.Instances.

Require Import Morphisms.
Require Import List.

Notation "ts [[ tid  :=  p ]]" := (thread_upd ts tid (Some p))
                                    (at level 12, left associativity).
Notation "ts [[ - tid ]]" := (thread_upd ts tid None)
                               (at level 12, left associativity).

Definition TID := nat.
Implicit Types (tid:TID).

Inductive event :=
| Event T (x:T).

Definition trace := list (TID * event).
Definition add_id tid (evs: list event) : trace := map (pair tid) evs.

Definition etrace {A B} (x: A * B * trace) : trace := let '(_, _, tr) := x in tr.

Instance Set_etrace A B : Setter (etrace (A:=A) (B:=B)).
Proof.
  refine {| set := fun f '(a, b, tr) => (a, b, f tr); |};
    intros;
    destruct matches.
Defined.

Section Execution.
  Variable Op:Type.
  Variable State:Type.
  Definition InstStep := Op -> State -> State -> list event -> Prop.
  Variable step: InstStep.
  Implicit Types (op:Op) (p: proc Op) (s:State) (tr:trace).

  Inductive proc_step tid : Relation (proc Op * State * trace) :=
  | exec_op : forall op s s' evs,
      step op s s' evs ->
      forall p' tr, proc_step tid
                         (Exec (Call op) p', s, tr)
                         (p', s', tr ++ add_id tid evs)
  .

  Notation threads := (threads_state (proc Op)).
  Implicit Types (ts:threads).

  Inductive exec_at tid : Relation (threads * State * trace) :=
  | exec_proc : forall ts p p',
      ts tid = Some p ->
      forall s s' tr tr',
        proc_step tid (p, s, tr) (p', s', tr') ->
        exec_at tid (ts, s, tr) (ts [[tid := p']], s', tr')
  | exec_atomic : forall ts p p',
      ts tid = Some (Exec (Atomic p) p') ->
      forall s s' tr tr',
        kleene_star (proc_step tid) (p, s, tr) (Ret, s', tr') ->
        exec_at tid (ts, s, tr) (ts [[tid := p']], s', tr')
  | exec_spawn : forall ts p p',
      ts tid = Some (Exec (Spawn p) p') ->
      forall tid',
        tid <> tid' ->
        ts tid' = None ->
        forall s tr, exec_at tid (ts, s, tr) (ts [[tid := p']] [[tid' := p]], s, tr)
  | exec_terminate : forall ts op p,
      ts tid = Some (Ret) ->
      forall s tr, exec_at tid (ts, s, tr) (ts [[-tid]], s, tr)
  .

  Definition exec_step : Relation (threads * State * trace) :=
    fun '(ts, s, tr) '(ts', s', tr') =>
      exists tid, exec_at tid (ts, s, tr) (ts', s', tr').

  Theorem thread_upd_aba_ba : forall ts tid tid' p1 p2 p3,
      ts [[tid := p1]] [[tid' := p2]] [[tid := p3]] =
      ts [[tid' := p2]] [[tid := p3]].
  Proof.
    intros.
    cmp_ts tid tid'.
    rewrite thread_upd_ne_comm with (tid:=tid) (tid':=tid') by auto;
      autorewrite with t;
      auto.
  Qed.

  Theorem thread_upd_aba : forall ts tid tid' p1 p2 p3,
      tid <> tid' ->
      ts [[tid := p1]] [[tid' := p2]] [[tid := p3]] =
      ts [[tid := p3]] [[tid' := p2]].
  Proof.
    intros.
    rewrite thread_upd_aba_ba.
    rewrite thread_upd_ne_comm; auto.
  Qed.

  Hint Rewrite thread_upd_aba using solve [ auto ] : t.

  Hint Constructors exec_at.

  Theorem exec_step_inv : forall ts tid p s tr ts' s' tr',
      exec_step (ts [[tid := p]], s, tr) (ts', s', tr') ->
      exec_at tid (ts [[tid := p]], s, tr) (ts', s', tr') \/
      exists tid', tid <> tid' /\
              exec_at tid' (ts [[tid := p]], s, tr) (ts' [[tid := p]], s', tr').
  Proof.
    intros.
    intuition eauto.
    unfold exec_step in H; propositional.
    cmp_ts tid tid0; eauto.
    right; exists tid0; intuition eauto.
    invert H; autorewrite with t in *; eauto.
    - cmp_ts tid tid'.
      rewrite thread_upd_same_eq with
        (ts:=ts [[tid := p]] [[tid0 := p']] [[tid' := p0]]);
        autorewrite with t;
        auto.
    - rewrite thread_upd_ne_comm with (tid := tid0) (tid' := tid) by auto;
        autorewrite with t;
        eauto.
  Qed.

  Definition exec := kleene_star exec_step.

  Theorem proc_step_prepend : forall tid tr0,
      Proper (proc_step tid ==> proc_step tid) (set etrace (app tr0)).
  Proof.
    unfold Proper, "==>"; intros.
    cbv [set Set_etrace]; destruct matches; subst.
    invert H.
    rewrite app_assoc; eauto using proc_step.
  Qed.

  Theorem kleene_star_proper : forall A (R: Relation A) (f: A -> A),
      Proper (R ==> R) f ->
      Proper (kleene_star R ==> kleene_star R) f.
  Proof.
    unfold Proper, "==>"; intros.
    induction H0; eauto using kleene_star.
  Qed.

  Theorem proc_step_star_prepend : forall tid tr0,
      Proper (kleene_star (proc_step tid) ==> kleene_star (proc_step tid))
             (set etrace (app tr0)).
  Proof.
    intros.
    apply kleene_star_proper.
    apply proc_step_prepend.
  Qed.

  Theorem exec_tr_prepend : forall tr0,
      Proper (exec_step ==> exec_step) (set etrace (app tr0)).
  Proof.
    unfold Proper, "==>"; intros.
    cbv [set Set_etrace]; destruct matches; subst.
    unfold exec_step in *; propositional.
    exists tid.
    invert H; eauto using exec_at.
    eapply exec_proc; eauto.
    apply (proc_step_prepend tr0) in H7; simpl in *; eauto.
    apply (proc_step_star_prepend tr0) in H7; simpl in *; eauto.
  Qed.

End Execution.

Local Notation proc_step_pat := (proc_step _ _ _ _).

Tactic Notation "check_pat" uconstr(pat) :=
  let x := constr:(ltac:(tryif assert_succeeds refine pat
                          then exact True
                          else refine pat) : Prop) in idtac.

Goal True. check_pat proc_step_pat. Abort.

Ltac inv_proc_step :=
  match goal with
  | [ H: proc_step_pat |- _ ] =>
    invert H
  end.
