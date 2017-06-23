Require Import Automation.

(* Modeling of programs. *)

Global Set Implicit Arguments.

(** The type of w that programs manipulate. Will vary depending on the
  operations involved,and the same operations could in principle operate on
  different types of w. *)
Parameter world:Type.

Implicit Type (w:world).

(* As a technical detail, we let programs include arbitrary operations of types
[opT T] (which will produce a T-typed result). *)
Parameter opT: Type -> Type.

(** Our minimal, generic programming language. This definition does not provide
useful functionality (it will be assumed later when we introduce primitives).
Programs can be combined with [Bind] and [Ret].

 Why do we even have BaseOp? The intention here is that programs should have
 opaque behavior, so we make sure that one of the constructors of [prog] allows
 arbitrary additional behavior. Otherwise, we would know that [Bind] and [Ret]
 are only enough for pure programs that do not have side effects.
 *)
CoInductive prog : forall T:Type, Type :=
| BaseOp : forall T, opT T -> prog T
| Ret : forall T, T -> prog T
| Bind : forall T T', prog T -> (T -> prog T') -> prog T'.

(** A Semantics is a transition relation for a particular program, relating an
initial state to a return value and final state. *)
Definition Semantics world T := world -> T -> world -> Prop.

(** The outcome of an execution, including intermediate crash points. *)
Inductive Result T :=
| Finished (v:T) (w:world)
| Crashed (w:world).
Arguments Crashed {T} w.

(* Programs may have arbitrary behavior for each primitive. *)
Axiom step:forall T, opT T -> Semantics world T.

(* On crash, the world state is modified to remove mutable data according to
[world_crash]. Not that this is a function; it should be a deterministic
process to replace in-memory state with default values. *)
Axiom world_crash: world -> world.

(* Can crashes happen?  This is effectively a flag that we will use in early
lab assignments to avoid having to reason about crashes. *)
Parameter can_crash: Prop.

(** [exec] specifies the execution semantics of complete programs using [step]
  as the small-step semantics of the primitive operations.

   Note that crashing is entirely modeled here: operations are always atomic,
   but otherwise crashes can occur before or after any operation. *)
Inductive exec : forall T, prog T -> world -> Result T -> Prop :=
| ExecOp : forall T (op: opT T) w v w',
    step op w v w' ->
    exec (BaseOp op) w (Finished v w')
| ExecOpCrashEnd : forall T (op: opT T) w v w',
    can_crash ->
    step op w v w' ->
    exec (BaseOp op) w (Crashed w')
| ExecCrashBegin : forall T (p: prog T) w,
    can_crash ->
    exec p w (Crashed w)
| ExecRet : forall T (v:T) w,
    exec (Ret v) w (Finished v w)
| ExecRetCrash : forall T (v:T) w,
    can_crash ->
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
 *)
Inductive exec_recover R (rec:prog R) (w:world) : R -> world -> Prop :=
| ExecRecoverExec : forall v w',
    exec rec w (Finished v w') ->
    exec_recover rec w v w'
| ExecRecoverCrashDuringRecovery : forall w' v w'',
    exec rec w (Crashed w') ->
    exec_recover rec (world_crash w') v w'' ->
    exec_recover rec w v w''.

(** [rexec] gives semantics for running a program and using some recovery
      procedure on crashes, including crashes during recovery.

     Similar to [exec] above, behavior for recovery is specified entirely here.
     In particular, note that we (currently) recovery from exactly the crash
     w - in practice, some semantics record mutable w as some subset of
     [world]s, which should be discarded before recovery.

     Note that this is a thin wrapper that chains execution and recovery
     self-execution - the constructors are not recursive.
 *)
Inductive rexec T R : prog T -> prog R -> world -> RResult T R -> Prop :=
| RExec : forall (p:prog T) (rec:prog R) w v w',
    exec p w (Finished v w') ->
    rexec p rec w (RFinished v w')
| RExecCrash : forall (p:prog T) (rec:prog R) w w' rv w'',
    exec p w (Crashed w') ->
    exec_recover rec (world_crash w') rv w'' ->
    rexec p rec w (Recovered rv w'').

Notation "x <- p1 ; p2" := (Bind p1 (fun x => p2))
                            (at level 60, right associativity).

Arguments Ret {T} v.

Global Generalizable Variables T R State step.

(** * Automation for inverting execution behavior. *)

Local Ltac inv_exec' H :=
  inversion H; subst; clear H; repeat sigT_eq.

Lemma exec_ret : forall T (v:T) w r,
    exec (Ret v) w r ->
    match r with
    | Finished v' w' => v = v' /\ w = w'
    | Crashed w' => w = w' /\ can_crash
    end.
Proof.
  intros.
  inv_exec' H; intuition.
Qed.

Ltac inv_ret :=
  match goal with
  | [ H: exec (Ret _) _ _ |- _ ] =>
    apply exec_ret in H; safe_intuition; subst
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
  | [ H: rexec (Ret _) _ _ _ |- _ ] =>
    inv_exec' H
  | [ H: rexec _ _ _ _ |- _ ] =>
    inv_exec' H
  end.
