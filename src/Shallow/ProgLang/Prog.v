Require Import EquivDec.

Require Import Automation.
Require Import Disk.

(* Modeling of programs with generic operations. *)

Global Set Implicit Arguments.

Section Prog.

  (** The type of operations (more precisely, the family of operation). An [opT
  T] is a primitive operation that produces a T-typed result. Of course, there
  need not be an [opT T] for every T. *)
  Variable opT: Type -> Type.

  (** Our minimal, generic programming language. Operations are provided as
  primitives using [Prim], and programs can be combined with [Bind] and include
  arbitrary intermediate values using [Ret]. *)
  Inductive prog : forall T:Type, Type :=
  | Prim : forall T, opT T -> prog T
  | Ret : forall T, T -> prog T
  | Bind : forall T T', prog T -> (T -> prog T') -> prog T'.

  (** The type of state that programs manipulate. Will vary depending on the
  operations involved,and the same operations could in principle operate on
  different types of state. *)
  Variable State:Type.

  (** A Semantics for a particular operation family and state type specifies
  what each primitive returns and how it changes the state.

  For some [step] of type [Semantics], [step op state v state'] means that operation
  [op] when executed from state [state] returns [v] and leaves the state at [state'].
  Note that the semantics might not specify any behavior for some input states -
  these are similar to non-termination, in that these states are ignored by any
  Hoare specification. *)
  Definition Semantics :=
    forall T, opT T -> State -> T -> State -> Prop.

  (** The outcome of an execution, including intermediate crash points. *)
  Inductive Result T :=
  | Finished (v:T) (state:State)
  | Crashed (state:State).
  Arguments Crashed {T} state.

  Variable step:Semantics.

  (** [exec] specifies the execution semantics of complete programs using [step]
  as the small-step semantics of the primitive operations.

   Note that crashing is entirely modeled here: operations are always atomic,
   but otherwise crashes can occur before or after any operation. *)
  Inductive exec : forall T, prog T -> State -> Result T -> Prop :=
  | ExecOp : forall T (op: opT T) state v state',
      step op state v state' ->
      exec (Prim op) state (Finished v state')
  | ExecOpCrashBegin : forall T (op: opT T) state,
      exec (Prim op) state (Crashed state)
  | ExecOpCrashEnd : forall T (op: opT T) state v state',
      step op state v state' ->
      exec (Prim op) state (Crashed state')
  | ExecRet : forall T (v:T) state,
      exec (Ret v) state (Finished v state)
  | ExecRetCrash : forall T (v:T) state,
      exec (Ret v) state (Crashed state)
  | ExecBindFinished : forall T T' (p: prog T) (p': T -> prog T')
                 state v state' r,
      exec p state (Finished v state') ->
      exec (p' v) state' r ->
      exec (Bind p p') state r
  | ExecBindCrashed : forall T T' (p: prog T) (p': T -> prog T')
                        state state',
      exec p state (Crashed state') ->
      exec (Bind p p') state (Crashed state').

  (** analogous to [Result] for recovery *)
  Inductive RResult T R :=
  | RFinished (v:T) (state:State)
  | Recovered (v:R) (state:State).

  Arguments RFinished {T R} v state.
  Arguments Recovered {T R} v state.

  (** Run rec in state until it finishes, restarting whenever it crashes.

   This models running rec in an infinite retry loop.

   TODO: after every crash should insert a crash relation step
   *)
  Inductive exec_recover R (rec:prog R) (state:State) : R -> State -> Prop :=
  | ExecRecoverExec : forall v state',
      exec rec state (Finished v state') ->
      exec_recover rec state v state'
  | ExecRecoverCrashDuringRecovery : forall state' v state'',
      exec rec state (Crashed state') ->
      exec_recover rec state' v state'' ->
      exec_recover rec state v state''.

  (** [rexec] gives semantics for running a program and using some recovery
      procedure on crashes, including crashes during recovery.

     Similar to [exec] above, behavior for recovery is specified entirely here.
     In particular, note that we (currently) recovery from exactly the crash
     state - in practice, some semantics record mutable state as some subset of
     [State]s, which should be discarded before recovery.

     Note that this is a thin wrapper that chains execution and recovery
     self-execution - the constructors are not recursive.

     TODO: add a parameter for a crash relation here.
   *)
  Inductive rexec T R : prog T -> prog R -> State -> RResult T R -> Prop :=
  | RExec : forall (p:prog T) (rec:prog R) state v state',
      exec p state (Finished v state') ->
      rexec p rec state (RFinished v state')
  | RExecCrash : forall (p:prog T) (rec:prog R) state state' rv state'',
      exec p state (Crashed state') ->
      exec_recover rec state' rv state'' ->
      rexec p rec state (Recovered rv state'').

End Prog.

Notation "x <- p1 ; p2" := (Bind p1 (fun x => p2))
                             (at level 60, right associativity).

Arguments Prim {opT T} op.
Arguments Ret {opT T} v.
Arguments Bind {opT T T'} p p'.

Arguments Crashed {State T} state.
Arguments RFinished {State T R} v state.
Arguments Recovered {State T R} v state.

Global Generalizable Variables T opT State step.

(* modify a semantics by adding a background step before every operation *)
Definition background_step `(bg_step: State -> State -> Prop) `(step: Semantics opT State) :
  Semantics opT State :=
  fun T (op:opT T) state v state'' =>
    exists state', bg_step state state' /\
          step _ op state' v state''.

(* definition of when one semantics implies a weaker one *)
Definition semantics_impl opT State (step step': Semantics opT State) :=
  forall T (op: opT T) state v state',
    step _ op state v state' -> step' _ op state v state'.

(** * Automation for inverting execution behavior. *)

Local Ltac inv_exec' H :=
  inversion H; subst; clear H; repeat sigT_eq.

Ltac inv_ret :=
  match goal with
  | [ H: exec _ (Ret _) _ _ |- _ ] =>
    inv_exec' H
  end.

Ltac inv_exec :=
  match goal with
  | _ => inv_ret
  | [ H: exec _ (Bind _ _) _ _ |- _ ] =>
    inv_exec' H; repeat inv_ret
  | [ H: exec _ _ _ _ |- _ ] =>
    inv_exec' H; repeat inv_ret
  end.

Ltac inv_prim :=
  match goal with
  | [ H: exec _ (Prim _) _ _ |- _ ] =>
    inv_exec' H
  end.

(* [inversion_prim_exec] performs much the same function as inversion on an exec
relation for a [Prim op] with one key diffence: it re-uses the proof of the
[Finished v state'] case in the [Crashed state'] case. This allows the crash invariant
proof to re-use the postcondition in the case that the primitive fully executed
just before crashing. *)
Theorem inversion_prim_exec : forall `(op: opT T) `(step: Semantics opT State) state r,
    exec step (Prim op) state r ->
    forall (P: _ -> Prop),
      (forall v state', step _ op state v state' ->
               P (Finished v state')) ->
      (forall v state', step _ op state v state' ->
               P (Finished v state') ->
               P (Crashed state')) ->
      (P (Crashed state)) ->
      P r.
Proof.
  intros; inv_exec; eauto.
Qed.
