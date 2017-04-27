Require Import Prog.
Require Import Disk.

(* Defines prog, programs over a single disks. *)

(* TODO: need better names for these types - spstate and SPState for single disk
states are quite awkward. *)

Set Implicit Arguments.

Inductive prog : Type -> Type :=
| SRead (a:addr) : prog block
| SWrite (a:addr) (b:block) : prog unit
| Ret T (v:T) : prog T
| Bind T T' (p: prog T) (p': T -> prog T') : prog T'.

Record SPState :=
  SDisk { sdisk: disk }.

Definition rstep T (p:prog T) (pstate:SPState) : StepResult SPState T :=
  match p with
  | SRead a =>
    match (sdisk pstate) a with
    | Some v => StepTo v pstate
    | None => Fails
    end
  | SWrite a b =>
    match (sdisk pstate) a with
    | Some _ => let pstate' := SDisk (upd (sdisk pstate) a b) in
               StepTo tt pstate'
    | None => Fails
    end
  | Ret v => StepTo v pstate
  | Bind _ _ => NonDet
  end.

Inductive exec : forall T, prog T -> SPState -> Result SPState T -> Prop :=
| ExecStepTo : forall T (p:prog T) pstate v pstate',
    rstep p pstate = StepTo v pstate' ->
    exec p pstate (Finished v pstate')
| ExecStepFail : forall T (p:prog T) pstate,
    rstep p pstate = Fails ->
    exec p pstate Failed
| ExecCrashAfter : forall T (p: prog T) pstate v pstate',
    rstep p pstate = StepTo v pstate' ->
    exec p pstate (Crashed pstate')
| ExecBindFinished : forall T T' (p: prog T) (p': T -> prog T')
                       pstate v pstate' r,
    exec p pstate (Finished v pstate') ->
    exec (p' v) pstate' r ->
    exec (Bind p p') pstate r
| ExecCrashBefore : forall T (p: prog T) pstate,
    exec p pstate (Crashed pstate)
| ExecBindCrashed : forall T T' (p: prog T) (p': T -> prog T')
                      pstate pstate',
    exec p pstate (Crashed pstate') ->
    exec (Bind p p') pstate (Crashed pstate')
| ExecBindFailed : forall T T' (p: prog T) (p': T -> prog T')
                     pstate,
    exec p pstate Failed ->
    exec (Bind p p') pstate Failed.

Inductive exec_recover T R : prog T -> prog R -> SPState -> RResult SPState T R -> Prop :=
| RExec : forall (p:prog T) (rec:prog R) pstate v pstate',
    exec p pstate (Finished v pstate') ->
    exec_recover p rec pstate (RFinished v pstate')
| RExecFailed : forall (p:prog T) (rec:prog R) pstate,
    exec p pstate Failed ->
    exec_recover p rec pstate RFailed
| RExecCrash : forall (p:prog T) (rec:prog R) pstate pstate' r,
    exec p pstate (Crashed pstate') ->
    exec_recover (T:=R) rec rec pstate' r ->
    exec_recover p rec pstate (to_recovered r).
