Require Import Spec.Proc.
Require Import Spec.ThreadsState.

Require Import Helpers.KleeneStar.

Require Import List.

Notation "ts [[  tid := p  ]]" := (thread_upd ts tid (Some p)) (at level 11).
Notation "ts [[  - tid  ]]" := (thread_upd ts tid None) (at level 11).

Definition TID := nat.
Implicit Types (tid:TID).

Inductive event :=
| Event T (x:T).

Definition trace := list (TID * event).
Definition add_id tid (evs: list event) : trace := map (pair tid) evs.

Section Execution.
  Variable Op:Type.
  Variable State:Type.
  Variable step: Op -> State -> State -> list event -> Prop.
  Implicit Types (op:Op) (p: proc Op) (s:State) (tr:trace).

  Inductive proc_step tid : Relation (proc Op * State * trace) :=
  | exec_op : forall op s s' evs,
      step op s s' evs ->
      forall p' tr, proc_step tid (Exec (Call op) p', s, tr) (p', s', tr ++ add_id tid evs)
  .

  Notation threads := (threads_state (proc Op)).
  Implicit Types (ts:threads).

  Inductive exec_step : threads * State * trace -> threads * State * trace -> Prop :=
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

End Execution.
