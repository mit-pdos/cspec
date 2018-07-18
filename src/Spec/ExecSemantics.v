Require Import Trace.
Require Import ConcurProc.
Require Import Helpers.FinMap.

Global Set Implicit Arguments.
Global Generalizable All Variables.

Section Execution.

  Variable Op: Type -> Type.
  Variable State : Type.

  Definition OpSemantics := forall T, Op T -> nat -> State -> T -> State -> list event -> Prop.
  Variable op_step : OpSemantics.

  Definition until1 T (c : T -> bool)
                      (p : option T -> proc Op T)
                      (v : option T) :=
    Bind (p v) (fun x => if c x then Ret x else Until c p (Some x)).

  Inductive atomic_exec : forall T, proc Op T -> nat -> State ->
                                    T -> State -> list event -> Prop :=

  | AtomicRet : forall T tid (v : T) s,
    atomic_exec (Ret v) tid s v s nil

  | AtomicBind : forall T1 T2 tid (p1 : proc Op T1) (p2 : T1 -> proc Op T2)
                        s0 s1 s2 ev1 ev2 (v1 : T1) (v2 : T2),
    atomic_exec p1 tid s0 v1 s1 ev1 ->
    atomic_exec (p2 v1) tid s1 v2 s2 ev2 ->
    atomic_exec (Bind p1 p2) tid s0 v2 s2 (ev1 ++ ev2)

  | AtomicOp : forall T tid (v : T) s s' op evs,
    op_step op tid s v s' evs ->
    atomic_exec (Call op) tid s v s' evs

  | AtomicUntil : forall T (p : option T -> proc Op T) (c : T -> bool) v tid s r s' ev',
    atomic_exec (until1 c p v) tid s r s' ev' ->
    atomic_exec (Until c p v) tid s r s' ev'
  .

  Inductive exec_tid : forall T (tid : nat),
    State -> proc Op T ->
    State -> T + proc Op T -> maybe_proc Op -> list event -> Prop :=

  | ExecTidRet : forall tid T (v : T) s,
    exec_tid tid s (Ret v)
                 s (inl v)
                 NoProc nil

  | ExecTidOp : forall tid T (v : T) s s' op evs,
    op_step op tid s v s' evs ->
    exec_tid tid s (Call op)
                 s' (inl v)
                 NoProc evs

  | ExecTidAtomic : forall tid T (v : T) ap s s' evs,
    atomic_exec ap tid s v s' evs ->
    exec_tid tid s (Atomic ap)
                 s' (inl v)
                 NoProc evs

  | ExecTidBind : forall tid T1 (p1 : proc Op T1) T2 (p2 : T1 -> proc Op T2) s s' result spawned evs,
    exec_tid tid s p1
                 s' result spawned evs ->
    exec_tid tid s (Bind p1 p2)
                 s' (inr
                     match result with
                     | inl r => p2 r
                     | inr p1' => Bind p1' p2
                     end
                    ) spawned evs

  | ExecTidUntil : forall tid T (p : option T -> proc Op T) (c : T -> bool) v s,
    exec_tid tid s (Until c p v)
                 s (inr (until1 c p v))
                 NoProc nil

  | ExecTidSpawn : forall tid T (p: proc Op T) s,
    exec_tid tid s (Spawn p)
                 s (inl tt)
                 (Proc p) nil
  .


  Inductive exec : State -> threads_state Op -> trace -> Prop :=

  | ExecOne : forall T tid tid' (ts : threads_state Op) trace p s s' evs result spawned,
    ts tid = @Proc Op T p ->
    ts tid' = NoProc ->
    exec_tid tid s p s' result spawned evs ->
    exec s' (thread_upd (thread_upd ts tid' spawned) tid
              match result with
              | inl _ => NoProc
              | inr p' => Proc p'
              end) trace ->
    exec s ts (prepend tid evs trace)

  | ExecStop : forall (ts : threads_state Op) s,
    exec s ts TraceEmpty.

End Execution.

Hint Constructors exec.

Notation "ts [[ tid ]]" := (thread_get ts tid)
  (at level 12, left associativity).

Notation "ts [[ tid := p ]]" := (thread_upd ts tid p)
                                  (at level 12, left associativity).
