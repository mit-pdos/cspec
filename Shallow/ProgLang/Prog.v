Require Import EquivDec.

Require Import Automation.
Require Import Disk.

(* Modeling of programs with generic operations. *)

Global Set Implicit Arguments.

Section Prog.

  Variable opT: Type -> Type.

  Inductive prog : forall T:Type, Type :=
  | Prim : forall T, opT T -> prog T
  | Ret : forall T, T -> prog T
  | Bind : forall T T', prog T -> (T -> prog T') -> prog T'.

  Variable State:Type.

  Definition Semantics :=
    forall T, opT T -> State -> T -> State -> Prop.

  Inductive Result T :=
  | Finished (v:T) (state:State)
  | Crashed (state:State).
  Arguments Crashed {T} state.

  Variable step:Semantics.

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

  Definition to_recovered {T R} (r:RResult R R) : RResult T R :=
    match r with
    | RFinished _ v pstate => Recovered _ v pstate
    | Recovered _ v pstate => Recovered _ v pstate
    end.

  Inductive exec_recover T R : prog T -> prog R -> State -> RResult T R -> Prop :=
  | RExec : forall (p:prog T) (rec:prog R) state v state',
      exec p state (Finished v state') ->
      exec_recover p rec state (RFinished _ v state')
  | RExecCrash : forall (p:prog T) (rec:prog R) state state' r,
      exec p state (Crashed state') ->
      exec_recover (T:=R) rec rec state' r ->
      exec_recover p rec state (to_recovered r).

End Prog.

Notation "x <- p1 ; p2" := (Bind p1 (fun x => p2))
                             (at level 60, right associativity).

Arguments Prim {opT T} op.
Arguments Ret {opT T} v.
Arguments Bind {opT T T'} p p'.
Arguments Crashed {State T} state.

Global Generalizable Variables T opT State step.

(* modify a semantics by adding a background step before every operation *)
Definition background_step `(bg_step: State -> State -> Prop) `(step: Semantics opT State) :
  Semantics opT State :=
  fun T (op:opT T) state v state'' =>
    exists state', bg_step state state' /\
          step _ op state' v state''.

Ltac inv_exec :=
  match goal with
  | [ H: exec _ _ _ _ |- _ ] =>
    inversion H; subst; clear H;
    repeat sigT_eq
  end.
