Require Import Prog.
Require Import Mem.

(* Defines seq_prog, sequential programs over sequential disks. *)

Set Implicit Arguments.

Inductive seq_prog : Type -> Type :=
| SRead (a:addr) : seq_prog block
| SWrite (a:addr) (b:block) : seq_prog unit
| Ret T (v:T) : seq_prog T
| Bind T T' (p: seq_prog T) (p': T -> seq_prog T') : seq_prog T'.

Record SSigma :=
  SDisk { sdisk: disk }.

Definition rstep T (p:seq_prog T) (sigma:SSigma) : StepResult SSigma T :=
  match p with
  | SRead a =>
    match (sdisk sigma) a with
    | Some v => StepTo v sigma
    | None => Fails
    end
  | SWrite a b =>
    match (sdisk sigma) a with
    | Some _ => let sigma' := SDisk (upd (sdisk sigma) a b) in
               StepTo tt sigma'
    | None => Fails
    end
  | Ret v => StepTo v sigma
  | Bind _ _ => NonDet
  end.

Inductive exec : forall T, seq_prog T -> SSigma -> Result SSigma T -> Prop :=
| ExecStepTo : forall T (p:seq_prog T) sigma v sigma',
    rstep p sigma = StepTo v sigma' ->
    exec p sigma (Finished v sigma')
| ExecStepFail : forall T (p:seq_prog T) sigma,
    rstep p sigma = Fails ->
    exec p sigma Failed
| ExecCrashAfter : forall T (p: seq_prog T) sigma v sigma',
    rstep p sigma = StepTo v sigma' ->
    exec p sigma (Crashed sigma')
| ExecBindFinished : forall T T' (p: seq_prog T) (p': T -> seq_prog T')
                       sigma v sigma' r,
    exec p sigma (Finished v sigma') ->
    exec (p' v) sigma' r ->
    exec (Bind p p') sigma r
| ExecCrashBefore : forall T (p: seq_prog T) sigma,
    exec p sigma (Crashed sigma)
| ExecBindCrashed : forall T T' (p: seq_prog T) (p': T -> seq_prog T')
                      sigma sigma',
    exec p sigma (Crashed sigma') ->
    exec (Bind p p') sigma (Crashed sigma')
| ExecBindFailed : forall T T' (p: seq_prog T) (p': T -> seq_prog T')
                     sigma,
    exec p sigma Failed ->
    exec (Bind p p') sigma Failed.

Inductive exec_recover : forall T R, seq_prog T -> seq_prog R -> SSigma -> RResult SSigma T R -> Prop :=
| RExec : forall T R (p:seq_prog T) (rec:seq_prog R) sigma v sigma',
    exec p sigma (Finished v sigma') ->
    exec_recover p rec sigma (RFinished v sigma')
| RExecFailed : forall T R (p:seq_prog T) (rec:seq_prog R) sigma,
    exec p sigma Failed ->
    exec_recover p rec sigma RFailed
| RExecCrash : forall T R (p:seq_prog T) (rec:seq_prog R) sigma sigma' r,
    exec p sigma (Crashed sigma') ->
    exec_recover rec rec sigma' r ->
    exec_recover p rec sigma (to_recovered r).

(* Local Variables: *)
(* company-coq-local-symbols: (("Sigma" . ?Σ) ("sigma" . ?σ) ("sigma'" . (?σ (Br . Bl) ?'))) *)
(* End: *)