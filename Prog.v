Require Import Mem.
Require Import Bytes.

(* Modeling of programs that use 3 synchronous disks. *)

Set Implicit Arguments.

Definition addr := nat.
Definition block := bytes 4096.

Inductive diskId := d0 | d1 | d2.

(** A [prog T] is a program that executes to a T-typed result. Programs may
manipulate disks with the primitive Read, Write, and Sync opcodes. *)
Inductive prog3 : Type -> Type :=
| Read (i:diskId) (a:addr) : prog3 block
| Write (i:diskId) (a:addr) (b:block) : prog3 unit
| Ret T (v:T) : prog3 T
| Bind T T' (p: prog3 T) (p': T -> prog3 T') : prog3 T'.

Definition disk := mem addr block.

(** The state the program manipulates as it executes. *)
Record Sigma :=
  Disks { disk0 : disk;
          disk1 : disk;
          disk2 : disk }.

(** Get a particular disk from a state by id. *)
Definition disk_id (i:diskId) (sigma:Sigma) : disk :=
  match i with
  | d0 => disk0 sigma
  | d1 => disk1 sigma
  | d2 => disk2 sigma
  end.

(** Apply an update function [up] to the disk identified by [i] in the state
[sigma]. *)
Definition upd_disk (i:diskId) (sigma:Sigma) (up:disk -> disk) : Sigma :=
  match i with
  | d0 => let 'Disks d_0 d_1 d_2 := sigma in Disks (up d_0) d_1 d_2
  | d1 => let 'Disks d_0 d_1 d_2 := sigma in Disks d_0 (up d_1) d_2
  | d2 => let 'Disks d_0 d_1 d_2 := sigma in Disks d_0 d_1 (up d_2)
  end.

(** A [StepResult] is the result of executing a program - it may give a final
outcome and return value, or report that the program fails. A third option
[NonDet] allows a StepResult to not specify any behavior for a program,
potentially under only certain conditions. *)
Inductive StepResult Sigma T :=
| StepTo (v:T) (sigma:Sigma)
| Fails
| NonDet.
Arguments Fails {Sigma T}.
Arguments NonDet {Sigma T}.

(** [step] gives each primitive operation a semantics by specifying how the
state is transformed and giving a return value of the appropriate type. *)
Definition step T (p:prog3 T) (sigma:Sigma) : StepResult Sigma T :=
  match p with
  | Read i a =>
    match (disk_id i sigma) a with
    | Some v => StepTo v sigma
    | None => Fails
    end
  | Write i a b =>
    match (disk_id i sigma) a with
    | Some _ => let sigma' := upd_disk i sigma (fun d => upd d a b) in
               StepTo tt sigma'
    | None => Fails
    end
  | Ret v => StepTo v sigma
  | Bind _ _ => NonDet
  end.

(** A [Result] is the outcome from running a program. *)
Inductive Result Sigma T :=
  (** the program finished, returning v and leaving the state at [sigma] *)
| Finished (v:T) (sigma:Sigma)
(** the program could crash at some intermediate point in state [sigma] (the return
value is in memory and is thus lost) *)
| Crashed (sigma:Sigma)
(** the program failed by attempting some illegal operation, eg, an
out-of-bounds write *)
| Failed.
Arguments Crashed {Sigma T} sigma.
Arguments Failed {Sigma T}.

(** Finally [exec] gives the semantics of a whole program. This combines
behavior of each individual instruction given by [step] with [Bind], which
sequentially composes programs, and crashes, which can expose any intermediate
state of a program. *)
Inductive exec : forall T, prog3 T -> Sigma -> Result Sigma T -> Prop :=
| ExecStepTo : forall T (p:prog3 T) sigma v sigma',
    step p sigma = StepTo v sigma' ->
    exec p sigma (Finished v sigma')
| ExecStepFail : forall T (p:prog3 T) sigma,
    step p sigma = Fails ->
    exec p sigma Failed
| ExecCrashAfter : forall T (p: prog3 T) sigma v sigma',
    step p sigma = StepTo v sigma' ->
    exec p sigma (Crashed sigma')
| ExecBindFinished : forall T T' (p: prog3 T) (p': T -> prog3 T')
                     sigma v sigma' r,
    exec p sigma (Finished v sigma') ->
    exec (p' v) sigma' r ->
    exec (Bind p p') sigma r
| ExecCrashBefore : forall T (p: prog3 T) sigma,
    exec p sigma (Crashed sigma)
| ExecBindCrashed : forall T T' (p: prog3 T) (p': T -> prog3 T')
                   sigma sigma',
    (* Note: this introduces some executions redundant with ExecCrashBefore,
    since the bind can directly crash using ExecCrashBefore or its first
    component can use ExecCrashBefore and then the bind uses this
    constructor. *)
    exec p sigma (Crashed sigma') ->
    exec (Bind p p') sigma (Crashed sigma')
| ExecBindFailed : forall T T' (p: prog3 T) (p': T -> prog3 T')
                   sigma,
    exec p sigma Failed ->
    exec (Bind p p') sigma Failed.

(** analogous to [Result] for recovery *)
Inductive RResult Sigma T R :=
| RFinished (v:T) (sigma:Sigma)
| Recovered (v:R) (sigma:Sigma)
| RFailed.

Arguments RFinished {Sigma T R} v sigma.
Arguments Recovered {Sigma T R} v sigma.
Arguments RFailed {Sigma T R}.

(** mark a recovery result as always being recovered, since it was executed
after a crash *)
Definition to_recovered {Sigma T R} (r:RResult Sigma R R) : RResult Sigma T R :=
  match r with
  | RFinished v sigma => Recovered v sigma
  | Recovered v sigma => Recovered v sigma
  | RFailed => RFailed
  end.

Inductive exec_recover : forall T R, prog3 T -> prog3 R -> Sigma -> RResult Sigma T R -> Prop :=
| RExec : forall T R (p:prog3 T) (rec:prog3 R) sigma v sigma',
    exec p sigma (Finished v sigma') ->
    exec_recover p rec sigma (RFinished v sigma')
| RExecFailed : forall T R (p:prog3 T) (rec:prog3 R) sigma,
    exec p sigma Failed ->
    exec_recover p rec sigma RFailed
| RExecCrash : forall T R (p:prog3 T) (rec:prog3 R) sigma sigma' r,
    exec p sigma (Crashed sigma') ->
    exec_recover rec rec sigma' r ->
    exec_recover p rec sigma (to_recovered r).

Notation "x <- p1 ; p2" := (Bind p1 (fun x => p2))
                            (at level 60, right associativity).
Notation "'do' x .. y <- p1 ; p2" := (Bind p1 (fun x => .. (fun y => p2) ..))
                                      (at level 60, right associativity,
                                       x binder, y binder, only parsing).

(* Local Variables: *)
(* company-coq-local-symbols: (("Sigma" . ?Σ) ("sigma" . ?σ) ("sigma'" . (?σ (Br . Bl) ?'))) *)
(* End: *)
