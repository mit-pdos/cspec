Require Import Helpers.Helpers.
Require Import Helpers.ListStuff.
Require Import ConcurProc.
Require Import Equiv.
Require Import Omega.
Require Import FunctionalExtensionality.
Require Import Relations.Relation_Operators.
Require Import RelationClasses.
Require Import Morphisms.
Require Import List.
Require Import Compile.

Import ListNotations.

Global Set Implicit Arguments.
Global Generalizable All Variables.


(** Opcodes *)

Inductive opLoT : Type -> Type :=
| Acquire : opLoT unit
| Release : opLoT unit
| Read : opLoT nat
| Write : nat -> opLoT unit.

Inductive opMidT : Type -> Type :=
| Inc : opMidT nat
| Dec : opMidT nat.

Variable opHiT : Type -> Type.


(** State *)

Record State := mkState {
  Value : nat;
  Lock : option nat;
}.


(** Semantics *)

(**
 * These semantics have a built-in protocol for how threads
 * must interact with the state.  Namely, a thread cannot acquire
 * a lock that is already held; a thread cannot release another
 * thread's lock; a thread cannot read or write unless it is holding
 * the lock.
 *
 * Separately we should prove that a particular implementation
 * (e.g., ours) follows this protocol on top of a lower-level
 * semantics that does not enforce these rules.
 *
 * So, in our framework, a concurrency protocol (e.g., rely-guarantee)
 * seems to be an extra level of refinement with semantics that codify
 * protocol violations as undefined behavior?
 *)

Inductive lo_step : forall T, opLoT T -> nat -> State -> T -> State -> Prop :=
| StepAcquire : forall tid v,
  lo_step Acquire tid (mkState v None) tt (mkState v (Some tid))
| StepRelease : forall tid v,
  lo_step Release tid (mkState v (Some tid)) tt (mkState v None)
| StepRead : forall tid v,
  lo_step Read tid (mkState v (Some tid)) v (mkState v (Some tid))
| StepWrite : forall tid v0 v,
  lo_step (Write v) tid (mkState v0 (Some tid)) tt (mkState v (Some tid)).

Inductive mid_step : forall T, opMidT T -> nat -> State -> T -> State -> Prop :=
| StepInc : forall tid v,
  mid_step Inc tid (mkState v None) v (mkState (v + 1) None)
| StepDec : forall tid v,
  mid_step Dec tid (mkState v None) v (mkState (v - 1) None).

Hint Extern 1 (lo_step _ _ _ _ _) => econstructor.
Hint Extern 1 (mid_step _ _ _ _ _) => econstructor.

Ltac step_inv :=
  match goal with
  | H : lo_step _ _ _ _ _ |- _ =>
    inversion H; clear H; subst; repeat sigT_eq
  | H : mid_step _ _ _ _ _ |- _ =>
    inversion H; clear H; subst; repeat sigT_eq
  end.


(** Implementations *)

Definition inc_core : proc opLoT opMidT _ :=
  _ <- Op Acquire;
  v <- Op Read;
  _ <- Op (Write (v + 1));
  _ <- Op Release;
  Ret v.

Definition dec_core : proc opLoT opMidT _ :=
  _ <- Op Acquire;
  v <- Op Read;
  _ <- Op (Write (v - 1));
  _ <- Op Release;
  Ret v.

Definition compile_op T (op : opMidT T) : proc opLoT opMidT T :=
  match op with
  | Inc => inc_core
  | Dec => dec_core
  end.


(** Commutativity *)

Lemma acquire_right_mover :
  right_mover lo_step Acquire.
Proof.
  unfold right_mover; intros.
  repeat step_inv; congruence.
Qed.

Lemma release_left_mover :
  left_mover lo_step Release.
Proof.
  unfold left_mover; intros.
  repeat step_inv; congruence.
Qed.

Lemma read_both_mover :
  both_mover lo_step Read.
Proof.
  split.
  - unfold right_mover; intros.
    repeat step_inv; congruence.
  - unfold left_mover; intros.
    repeat step_inv; congruence.
Qed.

Lemma write_both_mover : forall v,
  both_mover lo_step (Write v).
Proof.
  split.
  - unfold right_mover; intros.
    repeat step_inv; congruence.
  - unfold left_mover; intros.
    repeat step_inv; congruence.
Qed.

Hint Resolve acquire_right_mover.
Hint Resolve release_left_mover.
Hint Resolve read_both_mover.
Hint Resolve write_both_mover.


(** Atomicity *)

Theorem inc_atomic : forall `(rx : _ -> proc _ _ T),
  hitrace_incl lo_step
    (Bind (hicall compile_op Inc) rx)
    (Bind (hicall (atomize compile_op) Inc) rx).
Proof.
  unfold hicall, atomize; simpl.
  unfold inc_core; intros.
Admitted.

Theorem dec_atomic : forall `(rx : _ -> proc _ _ T),
  hitrace_incl lo_step
    (Bind (hicall compile_op Dec) rx)
    (Bind (hicall (atomize compile_op) Dec) rx).
Proof.
  unfold hicall, atomize; simpl.
  unfold dec_core; intros.
Admitted.


(** Many-thread correctness *)

Theorem my_compile_correct :
  compile_correct opHiT compile_op lo_step mid_step.
Proof.
  unfold compile_correct; intros.
  destruct op.

  + repeat atomic_exec_inv.
    repeat step_inv.
    simpl; intuition eauto 20.

  + repeat atomic_exec_inv.
    repeat step_inv.
    simpl; intuition eauto 20.
Qed.

Theorem my_atomize_correct :
  atomize_correct compile_op lo_step.
Proof.
  unfold atomize_correct; intros.
  destruct op.
  + rewrite inc_atomic.
    eapply hitrace_incl_bind_a.
    eauto.
  + rewrite dec_atomic.
    eapply hitrace_incl_bind_a.
    eauto.
Qed.

Hint Resolve my_compile_correct.
Hint Resolve my_atomize_correct.


Theorem all_traces_match :
  forall ts1 (ts2 : @threads_state _ opHiT),
  proc_match (compile_ok compile_op) ts1 ts2 ->
  traces_match_ts lo_step mid_step ts1 ts2.
Proof.
  intros.
  eapply compile_traces_match_ts; eauto.
Qed.
