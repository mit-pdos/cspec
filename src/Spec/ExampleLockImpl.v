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
Require Import CompileLoop.

Import ListNotations.

Global Set Implicit Arguments.
Global Generalizable All Variables.


(** Opcodes *)

Inductive opLoT : Type -> Type :=
| TestAndSet : opLoT bool
| Clear : opLoT unit.

Inductive opMidT : Type -> Type :=
| Acquire : opMidT bool
| Release : opMidT unit.


(** State *)

Definition State := bool.


(** Semantics *)

Inductive lo_step : forall T, opLoT T -> nat -> State -> T -> State -> Prop :=
| LoStepTAS : forall tid v,
  lo_step TestAndSet tid v v true
| LoStepClear : forall tid v,
  lo_step Clear tid v tt false.

Inductive mid_step : forall T, opMidT T -> nat -> State -> T -> State -> Prop :=
| MidStepAcquire : forall tid r,
  mid_step Acquire tid false r true
| MidStepRelease : forall tid v,
  mid_step Release tid v tt false.

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

Definition acquire_cond (r : bool) :=
  if r == false then true else false.

Definition acquire_core : proc opLoT _ :=
  Until acquire_cond (Op TestAndSet).

Definition release_cond (r : unit) :=
  true.

Definition release_core : proc opLoT _ :=
  Until release_cond (Op Clear).

Definition compile_op T (op : opMidT T) : (opLoT T) * (T -> bool) :=
  match op with
  | Acquire => (TestAndSet, acquire_cond)
  | Release => (Clear, release_cond)
  end.


(** Proofs *)

Theorem acquire_noop_or_success :
  forall tid s r s',
    lo_step TestAndSet tid s r s' ->
    acquire_cond r = false /\ s = s' \/
    acquire_cond r = true /\ mid_step Acquire tid s r s'.
Proof.
  unfold acquire_cond; intros.
  step_inv.
  destruct (r == false); subst; eauto.
  destruct r; try congruence; eauto.
Qed.

Theorem release_noop_or_success :
  forall tid s r s',
    lo_step Clear tid s r s' ->
    release_cond r = false /\ s = s' \/
    release_cond r = true /\ mid_step Release tid s r s'.
Proof.
  unfold release_cond; intros.
  step_inv.
  eauto.
Qed.

Theorem all_noop_or_success :
  noop_or_success compile_op lo_step mid_step.
Proof.
  unfold noop_or_success.
  destruct opM; simpl; intros.
  - inversion H; clear H; subst.
    eapply acquire_noop_or_success; eauto.
  - inversion H; clear H; subst.
    eapply release_noop_or_success; eauto.
Qed.


Theorem compile_traces_match :
  forall ts,
    Compile.no_atomics_ts ts ->
    traces_match_ts lo_step mid_step (compile_ts compile_op ts) ts.
Proof.
  intros.
  eapply compile_traces_match_ts.
  eapply all_noop_or_success.
  eapply compile_ts_ok; eauto.
Qed.
