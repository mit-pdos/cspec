Require Import ProofIrrelevance.
Require Import EquivDec.

Require Import Automation.
Require Import Disk.

(* Modeling of programs that use 3 synchronous disks. *)

Set Implicit Arguments.

Inductive diskId := d0 | d1 | d2.

(** A [prog T] is a program that executes to a T-typed result. Programs may
manipulate disks with the primitive Read, Write, and Sync opcodes. *)
Inductive prog3 : Type -> Type :=
| Read (i:diskId) (a:addr) : prog3 block
| Write (i:diskId) (a:addr) (b:block) : prog3 unit
| Ret {T} (v:T) : prog3 T
| Bind T T' (p: prog3 T) (p': T -> prog3 T') : prog3 T'.

Definition disk := mem addr block.

(** The state the program manipulates as it executes. *)
Record PState :=
  Disks { disk0 : disk;
          disk1 : disk;
          disk2 : disk }.

(** Get a particular disk from a state by id. *)
Definition disk_id (i:diskId) (pstate:PState) : disk :=
  match i with
  | d0 => disk0 pstate
  | d1 => disk1 pstate
  | d2 => disk2 pstate
  end.

(** Apply an update function [up] to the disk identified by [i] in the state
[pstate]. *)
Definition upd_disk (i:diskId) (pstate:PState) (up:disk -> disk) : PState :=
  match i with
  | d0 => let 'Disks d_0 d_1 d_2 := pstate in Disks (up d_0) d_1 d_2
  | d1 => let 'Disks d_0 d_1 d_2 := pstate in Disks d_0 (up d_1) d_2
  | d2 => let 'Disks d_0 d_1 d_2 := pstate in Disks d_0 d_1 (up d_2)
  end.

(** A [StepResult] is the result of executing a program - it may give a final
outcome and return value, or report that the program fails. A third option
[NonDet] allows a StepResult to not specify any behavior for a program,
potentially under only certain conditions. *)
Inductive StepResult PState T :=
| StepTo (v:T) (pstate:PState)
| Fails
| NonDet.
Arguments Fails {PState T}.
Arguments NonDet {PState T}.

(** [step] gives each primitive operation a semantics by specifying how the
state is transformed and giving a return value of the appropriate type. *)
Definition step T (p:prog3 T) (pstate:PState) : StepResult PState T :=
  match p with
  | Read i a =>
    match (disk_id i pstate) a with
    | Some v => StepTo v pstate
    | None => Fails
    end
  | Write i a b =>
    match (disk_id i pstate) a with
    | Some _ => let pstate' := upd_disk i pstate (fun d => upd d a b) in
               StepTo tt pstate'
    | None => Fails
    end
  | Ret v => StepTo v pstate
  | Bind _ _ => NonDet
  end.

(** A [Result] is the outcome from running a program. *)
Inductive Result PState T :=
  (** the program finished, returning v and leaving the state at [pstate] *)
| Finished (v:T) (pstate:PState)
(** the program could crash at some intermediate point in state [pstate] (the return
value is in memory and is thus lost) *)
| Crashed (pstate:PState)
(** the program failed by attempting some illegal operation, eg, an
out-of-bounds write *)
| Failed.
Arguments Crashed {PState T} pstate.
Arguments Failed {PState T}.

(** Finally [exec] gives the semantics of a whole program. This combines
behavior of each individual instruction given by [step] with [Bind], which
sequentially composes programs, and crashes, which can expose any intermediate
state of a program. *)
Inductive exec : forall T, prog3 T -> PState -> Result PState T -> Prop :=
| ExecStepTo : forall T (p:prog3 T) pstate v pstate',
    step p pstate = StepTo v pstate' ->
    exec p pstate (Finished v pstate')
| ExecStepFail : forall T (p:prog3 T) pstate,
    step p pstate = Fails ->
    exec p pstate Failed
| ExecCrashBefore : forall T (p: prog3 T) pstate,
    exec p pstate (Crashed pstate)
| ExecCrashAfter : forall T (p: prog3 T) pstate v pstate',
    step p pstate = StepTo v pstate' ->
    exec p pstate (Crashed pstate')
| ExecBindFinished : forall T T' (p: prog3 T) (p': T -> prog3 T')
                     pstate v pstate' r,
    exec p pstate (Finished v pstate') ->
    exec (p' v) pstate' r ->
    exec (Bind p p') pstate r
| ExecBindCrashed : forall T T' (p: prog3 T) (p': T -> prog3 T')
                   pstate pstate',
    (* Note: this introduces some executions redundant with ExecCrashBefore,
    since the bind can directly crash using ExecCrashBefore or its first
    component can use ExecCrashBefore and then the bind uses this
    constructor. *)
    exec p pstate (Crashed pstate') ->
    exec (Bind p p') pstate (Crashed pstate')
| ExecBindFailed : forall T T' (p: prog3 T) (p': T -> prog3 T')
                   pstate,
    exec p pstate Failed ->
    exec (Bind p p') pstate Failed.

(** analogous to [Result] for recovery *)
Inductive RResult PState T R :=
| RFinished (v:T) (pstate:PState)
| Recovered (v:R) (pstate:PState)
| RFailed.

Arguments RFinished {PState T R} v pstate.
Arguments Recovered {PState T R} v pstate.
Arguments RFailed {PState T R}.

(** mark a recovery result as always being recovered, since it was executed
after a crash *)
Definition to_recovered {PState T R} (r:RResult PState R R) : RResult PState T R :=
  match r with
  | RFinished v pstate => Recovered v pstate
  | Recovered v pstate => Recovered v pstate
  | RFailed => RFailed
  end.

Inductive exec_recover T R : prog3 T -> prog3 R -> PState -> RResult PState T R -> Prop :=
| RExec : forall (p:prog3 T) (rec:prog3 R) pstate v pstate',
    exec p pstate (Finished v pstate') ->
    exec_recover p rec pstate (RFinished v pstate')
| RExecFailed : forall (p:prog3 T) (rec:prog3 R) pstate,
    exec p pstate Failed ->
    exec_recover p rec pstate RFailed
| RExecCrash : forall (p:prog3 T) (rec:prog3 R) pstate pstate' r,
    exec p pstate (Crashed pstate') ->
    exec_recover (T:=R) rec rec pstate' r ->
    exec_recover p rec pstate (to_recovered r).

Notation "x <- p1 ; p2" := (Bind p1 (fun x => p2))
                            (at level 60, right associativity).
Notation "'do' x .. y <- p1 ; p2" := (Bind p1 (fun x => .. (fun y => p2) ..))
                                      (at level 60, right associativity,
                                       x binder, y binder, only parsing).

(* A bit of automation to prove properties of executions. *)

Ltac inj_pair2 :=
  match goal with
  | [ H: existT ?P ?A _ = existT ?P ?A _ |- _ ] =>
    apply inj_pair2 in H; subst
  end.

Ltac inv_exec :=
  match goal with
  | [ H: exec _ _ _ |- _ ] =>
    inversion H; subst; clear H;
    repeat inj_pair2
  end.

Ltac simp_stepto :=
  match goal with
  | [ H: step _ _ = StepTo _ _ |- _ ] =>
    progress cbn [step] in H;
    destruct_nongoal_matches;
    inversion H; subst; clear H
  | [ H: step _ _ = Fails |- _ ] =>
    progress cbn [step] in H;
    destruct_nongoal_matches;
    inversion H; subst; clear H
  end.
