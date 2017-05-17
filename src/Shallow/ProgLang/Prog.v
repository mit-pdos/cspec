Require Import EquivDec.

Require Import Automation.
Require Import Disk.

(* Modeling of programs with generic operations. *)

Global Set Implicit Arguments.

(** The type of operations (more precisely, the family of operation). An [opT
  T] is a primitive operation that produces a T-typed result. Of course, there
  need not be an [opT T] for every T. *)
Parameter opT: Type -> Type.

(** The type of w that programs manipulate. Will vary depending on the
  operations involved,and the same operations could in principle operate on
  different types of w. *)
Parameter world:Type.

Implicit Type (w:world).

(** Our minimal, generic programming language. Operations are provided as
    primitives using [Prim], and programs can be combined with [Bind] and
    include arbitrary intermediate values using [Ret]. *)
Inductive prog : forall T:Type, Type :=
| Prim : forall T, opT T -> prog T
| Ret : forall T, T -> prog T
| Bind : forall T T', prog T -> (T -> prog T') -> prog T'.

(** A Semantics is a transition relation for a particular program. *)
Definition Semantics world T := world -> T -> world -> Prop.

(** The outcome of an execution, including intermediate crash points. *)
Inductive Result T :=
| Finished (v:T) (w:world)
| Crashed (w:world).
Arguments Crashed {T} w.

Axiom step:forall T, opT T -> Semantics world T.

(** [exec] specifies the execution semantics of complete programs using [step]
  as the small-step semantics of the primitive operations.

   Note that crashing is entirely modeled here: operations are always atomic,
   but otherwise crashes can occur before or after any operation. *)
Inductive exec : forall T, prog T -> world -> Result T -> Prop :=
| ExecOp : forall T (op: opT T) w v w',
    step op w v w' ->
    exec (Prim op) w (Finished v w')
| ExecOpCrashBegin : forall T (op: opT T) w,
    exec (Prim op) w (Crashed w)
| ExecOpCrashEnd : forall T (op: opT T) w v w',
    step op w v w' ->
    exec (Prim op) w (Crashed w')
| ExecRet : forall T (v:T) w,
    exec (Ret v) w (Finished v w)
| ExecRetCrash : forall T (v:T) w,
    exec (Ret v) w (Crashed w)
| ExecBindFinished : forall T T' (p: prog T) (p': T -> prog T')
                       w v w' r,
    exec p w (Finished v w') ->
    exec (p' v) w' r ->
    exec (Bind p p') w r
| ExecBindCrashed : forall T T' (p: prog T) (p': T -> prog T')
                      w w',
    exec p w (Crashed w') ->
    exec (Bind p p') w (Crashed w').

(** analogous to [Result] for recovery *)
Inductive RResult T R :=
| RFinished (v:T) (w:world)
| Recovered (v:R) (w:world).

Arguments RFinished {T R} v w.
Arguments Recovered {T R} v w.

(** Run rec in w until it finishes, restarting whenever it crashes.

   This models running rec in an infinite retry loop.

   TODO: after every crash should insert a crash relation step
 *)
Inductive exec_recover R (rec:prog R) (w:world) : R -> world -> Prop :=
| ExecRecoverExec : forall v w',
    exec rec w (Finished v w') ->
    exec_recover rec w v w'
| ExecRecoverCrashDuringRecovery : forall w' v w'',
    exec rec w (Crashed w') ->
    exec_recover rec w' v w'' ->
    exec_recover rec w v w''.

(** [rexec] gives semantics for running a program and using some recovery
      procedure on crashes, including crashes during recovery.

     Similar to [exec] above, behavior for recovery is specified entirely here.
     In particular, note that we (currently) recovery from exactly the crash
     w - in practice, some semantics record mutable w as some subset of
     [world]s, which should be discarded before recovery.

     Note that this is a thin wrapper that chains execution and recovery
     self-execution - the constructors are not recursive.

     TODO: add a parameter for a crash relation here.
 *)
Inductive rexec T R : prog T -> prog R -> world -> RResult T R -> Prop :=
| RExec : forall (p:prog T) (rec:prog R) w v w',
    exec p w (Finished v w') ->
    rexec p rec w (RFinished v w')
| RExecCrash : forall (p:prog T) (rec:prog R) w w' rv w'',
    exec p w (Crashed w') ->
    exec_recover rec w' rv w'' ->
    rexec p rec w (Recovered rv w'').

Notation "x <- p1 ; p2" := (Bind p1 (fun x => p2))
                            (at level 60, right associativity).

(* TODO: some of these might be redundant now *)
Arguments Prim {T} op.
Arguments Ret {T} v.
Arguments Bind {T T'} p p'.

Arguments Crashed {T} w.
Arguments RFinished {T R} v w.
Arguments Recovered {T R} v w.

Global Generalizable Variables T R opT State step.

(** * Automation for inverting execution behavior. *)

Local Ltac inv_exec' H :=
  inversion H; subst; clear H; repeat sigT_eq.

Ltac inv_ret :=
  match goal with
  | [ H: exec (Ret _) _ _ |- _ ] =>
    inv_exec' H
  end.

Ltac inv_exec :=
  match goal with
  | _ => inv_ret
  | [ H: exec (Bind _ _) _ _ |- _ ] =>
    inv_exec' H; repeat inv_ret
  | [ H: exec _ _ _ |- _ ] =>
    inv_exec' H; repeat inv_ret
  end.

Ltac inv_rexec :=
  match goal with
  | [ H: rexec _ _ _ _ |- _ ] =>
    inv_exec' H
  end.

Ltac inv_prim :=
  match goal with
  | [ H: exec (Prim _) _ _ |- _ ] =>
    inv_exec' H
  end.

(* [inversion_prim_exec] performs much the same function as inversion on an exec
relation for a [Prim op] with one key diffence: it re-uses the proof of the
[Finished v w'] case in the [Crashed w'] case. This allows the crash invariant
proof to re-use the postcondition in the case that the primitive fully executed
just before crashing. *)
Theorem inversion_prim_exec : forall `(op: opT T) w r,
    exec (Prim op) w r ->
    forall (P: _ -> Prop),
      (forall v w', step op w v w' ->
               P (Finished v w')) ->
      (forall v w', step op w v w' ->
               P (Finished v w') ->
               P (Crashed w')) ->
      (P (Crashed w)) ->
      P r.
Proof.
  intros; inv_exec; eauto.
Qed.
