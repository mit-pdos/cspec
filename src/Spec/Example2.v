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
Require Import Modules.
Require Import Movers.

Import ListNotations.

Global Set Implicit Arguments.
Global Generalizable All Variables.


(** Opcodes and states *)

Inductive LockOpT : Type -> Type :=
| Acquire : LockOpT unit
| Release : LockOpT unit
| Read : LockOpT nat
| Write : nat -> LockOpT unit.

Inductive CounterOpT : Type -> Type :=
| Inc : CounterOpT nat
| Dec : CounterOpT nat.

Record LockState := mkState {
  Value : nat;
  Lock : option nat;
}.

Definition CounterState := nat.


(** Layer definitions *)

Module LockAPI <: Layer.

  Definition opT := LockOpT.
  Definition State := LockState.

  (**
   * These semantics have a built-in protocol for how threads
   * must interact with the state.  Namely, a thread cannot acquire
   * a lock that is already held; a thread cannot release another
   * thread's lock; a thread cannot read or write unless it is holding
   * the lock.
   *
   * Separately we can prove that a particular implementation
   * (e.g., ours) follows this protocol on top of a lower-level
   * semantics that does not enforce these rules.  See ExampleProtocol.v.
   *
   * So, in our framework, a concurrency protocol (e.g., rely-guarantee)
   * seems to be an extra level of refinement with semantics that codify
   * protocol violations as undefined behavior?
   *)

  Inductive xstep : forall T, opT T -> nat -> State -> T -> State -> Prop :=
  | StepAcquire : forall tid v,
    xstep Acquire tid (mkState v None) tt (mkState v (Some tid))
  | StepRelease : forall tid v,
    xstep Release tid (mkState v (Some tid)) tt (mkState v None)
  | StepReleaseHack0 : forall tid v,
    xstep Release tid (mkState v None) tt (mkState v None)
  | StepReleaseHack1 : forall tid tid' v,
    tid' <> tid ->
    xstep Release tid (mkState v (Some tid')) tt (mkState v (Some tid'))
  | StepRead : forall tid v,
    xstep Read tid (mkState v (Some tid)) v (mkState v (Some tid))
  | StepWrite : forall tid v0 v,
    xstep (Write v) tid (mkState v0 (Some tid)) tt (mkState v (Some tid)).

  Definition step := xstep.

End LockAPI.


Module LockedCounterAPI <: Layer.

  Definition opT := CounterOpT.
  Definition State := LockState.

  Inductive xstep : forall T, opT T -> nat -> State -> T -> State -> Prop :=
  | StepInc : forall tid v,
    xstep Inc tid (mkState v None) v (mkState (v + 1) None)
  | StepDec : forall tid v,
    xstep Dec tid (mkState v None) v (mkState (v - 1) None).

  Definition step := xstep.

End LockedCounterAPI.


Module CounterAPI <: Layer.

  Definition opT := CounterOpT.
  Definition State := CounterState.

  Inductive xstep : forall T, opT T -> nat -> State -> T -> State -> Prop :=
  | StepInc : forall tid v,
    xstep Inc tid v v (v + 1)
  | StepDec : forall tid v,
    xstep Dec tid v v (v - 1).

  Definition step := xstep.

End CounterAPI.


(** Using locks to get atomicity. *)

Module LockingCounter <: LayerImpl LockAPI LockedCounterAPI.

  Definition inc_core : proc LockAPI.opT _ :=
    _ <- Op Acquire;
    v <- Op Read;
    _ <- Op (Write (v + 1));
    _ <- Op Release;
    Ret v.

  Definition dec_core : proc LockAPI.opT _ :=
    _ <- Op Acquire;
    v <- Op Read;
    _ <- Op (Write (v - 1));
    _ <- Op Release;
    Ret v.

  Definition compile_op T (op : LockedCounterAPI.opT T)
                        : proc LockAPI.opT T :=
    match op with
    | Inc => inc_core
    | Dec => dec_core
    end.

  Ltac step_inv :=
    match goal with
    | H : LockAPI.step _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : LockedCounterAPI.step _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    end.

  Hint Extern 1 (LockAPI.step _ _ _ _ _) => econstructor.
  Hint Extern 1 (LockedCounterAPI.step _ _ _ _ _) => econstructor.

  Lemma acquire_right_mover :
    right_mover LockAPI.step Acquire.
  Proof.
    unfold right_mover; intros.
    repeat step_inv; try congruence; eauto.
  Qed.

  Lemma release_left_mover :
    left_mover LockAPI.step Release.
  Proof.
    split.
    - unfold always_enabled; intros.
      destruct s. destruct Lock0. destruct (n == tid); subst.
      all: eauto.
    - unfold left_mover; intros.
      repeat step_inv; try congruence; eauto.
  Qed.

  Lemma read_right_mover :
    right_mover LockAPI.step Read.
  Proof.
    unfold right_mover; intros.
    repeat step_inv; try congruence; eauto.
  Qed.

  Lemma write_right_mover : forall v,
    right_mover LockAPI.step (Write v).
  Proof.
    unfold right_mover; intros.
    repeat step_inv; try congruence; eauto.
  Qed.

  Hint Resolve acquire_right_mover.
  Hint Resolve release_left_mover.
  Hint Resolve read_right_mover.
  Hint Resolve write_right_mover.


  Theorem inc_atomic : forall `(rx : _ -> proc _ T),
    trace_incl LockAPI.step
      (Bind (compile_op Inc) rx)
      (Bind (atomize compile_op Inc) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold inc_core; eauto 20.
  Qed.

  Theorem dec_atomic : forall `(rx : _ -> proc _ T),
    trace_incl LockAPI.step
      (Bind (compile_op Dec) rx)
      (Bind (atomize compile_op Dec) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold dec_core; eauto 20.
  Qed.

  Theorem my_compile_correct :
    compile_correct compile_op LockAPI.step LockedCounterAPI.step.
  Proof.
    unfold compile_correct; intros.
    destruct op.

    + repeat atomic_exec_inv.
      repeat step_inv.
      simpl; intuition eauto 20; compute; eauto.
      simpl; intuition eauto 20; compute; eauto.

    + repeat atomic_exec_inv.
      repeat step_inv.
      simpl; intuition eauto 20; compute; eauto.
      simpl; intuition eauto 20; compute; eauto.
  Qed.

  Theorem my_atomize_correct :
    atomize_correct compile_op LockAPI.step.
  Proof.
    unfold atomize_correct; intros.
    destruct op.
    + rewrite inc_atomic.
      eapply trace_incl_bind_a.
      eauto.
    + rewrite dec_atomic.
      eapply trace_incl_bind_a.
      eauto.
  Qed.

  Hint Resolve my_compile_correct.
  Hint Resolve my_atomize_correct.


  Theorem all_traces_match :
    forall ts1 ts2,
      proc_match (compile_ok compile_op) ts1 ts2 ->
      traces_match_ts LockAPI.step LockedCounterAPI.step ts1 ts2.
  Proof.
    intros.
    eapply compile_traces_match_ts; eauto.
  Qed.

  Definition absR (s1 : LockAPI.State) (s2 : LockedCounterAPI.State) :=
    s1 = s2.

  Definition compile_ts := compile_ts compile_op.

  Theorem compile_traces_match :
    forall ts2,
      traces_match_abs absR LockAPI.step LockedCounterAPI.step (compile_ts ts2) ts2.
  Proof.
    unfold traces_match_abs; intros.
    rewrite H0 in *; clear H0.
    eapply all_traces_match; eauto.
    eapply compile_ts_ok.
  Qed.

End LockingCounter.
