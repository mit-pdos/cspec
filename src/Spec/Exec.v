Require Import Spec.Proc.
Require Import Spec.ThreadsState.

Require Import Helpers.TransitionSystem.
Require Import Helpers.ProofAutomation.
Require Import Helpers.RecordSet.

Require Import Morphisms.
Require Import List.

Notation "ts [[ tid  :=  p ]]" := (thread_upd ts tid (Some p)) (at level 11).
Notation "ts [[ - tid ]]" := (thread_upd ts tid None) (at level 11).

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

  Inductive exec_step : Relation (threads * State * trace) :=
  | exec_proc : forall ts p p' tid,
      ts tid = Some p ->
      forall s s' tr tr',
        proc_step tid (p, s, tr) (p', s', tr') ->
        exec_step (ts, s, tr) (ts [[tid := p']], s', tr')
  | exec_atomic : forall ts p p' tid,
      ts tid = Some (Exec (Atomic p) p') ->
      forall s s' tr tr',
        kleene_star (proc_step tid) (p, s, tr) (Ret, s', tr') ->
        exec_step (ts, s, tr) (ts [[tid := p']], s', tr')
  | exec_spawn : forall ts p p' tid,
      ts tid = Some (Exec (Spawn p) p') ->
      forall tid',
        tid <> tid' ->
        forall s tr, exec_step (ts, s, tr) (ts [[tid := p']] [[tid' := p]], s, tr)
  | exec_terminate : forall ts op p tid,
      ts tid = Some (Ret) ->
      forall s tr, exec_step (ts, s, tr) (ts [[-tid]], s, tr)
  .

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
    invert H; eauto using exec_step.
    eapply exec_proc; eauto.
    apply (proc_step_prepend tr0) in H7; simpl in *; eauto.
    apply (proc_step_star_prepend tr0) in H7; simpl in *; eauto.
    eapply exec_atomic; eauto.
  Qed.

End Execution.
