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
Require Import CompileLoop.
Require Import Modules.
Require Import Movers.
Require Import Abstraction.
Require Import Protocol.

Import ListNotations.

Global Set Implicit Arguments.
Global Generalizable All Variables.


(** Opcodes and states *)

Inductive TASOpT : Type -> Type :=
| TestAndSet :TASOpT bool
| Clear : TASOpT unit
| ReadTAS : TASOpT nat
| WriteTAS : nat -> TASOpT unit.

Inductive LockOpT : Type -> Type :=
| Acquire : LockOpT bool
| Release : LockOpT unit
| Read : LockOpT nat
| Write : nat -> LockOpT unit.

Inductive CounterOpT : Type -> Type :=
| Inc : CounterOpT nat
| Dec : CounterOpT nat.

Record TASState := mkTASState {
  TASValue : nat;
  TASLock : bool;
}.

Record LockState := mkState {
  Value : nat;
  Lock : option nat;
}.

Definition CounterState := nat.


(** Layer definitions *)

Module TASAPI <: Layer.

  Definition opT := TASOpT.
  Definition State := TASState.

  Inductive xstep : forall T, opT T -> nat -> State -> T -> State -> Prop :=
  | StepTAS : forall tid v l,
    xstep TestAndSet tid (mkTASState v l) l (mkTASState v true)
  | StepClear : forall tid v l,
    xstep Clear tid (mkTASState v l) tt (mkTASState v false)
  | StepRead : forall tid v l,
    xstep ReadTAS tid (mkTASState v l) v (mkTASState v l)
  | StepWrite : forall tid v0 v l,
    xstep (WriteTAS v) tid (mkTASState v0 l) tt (mkTASState v l).

  Definition step := xstep.

  Definition initP s :=
    TASLock s = false.

End TASAPI.


Module TASLockAPI <: Layer.

  Definition opT := TASOpT.
  Definition State := LockState.

  Inductive xstep : forall T, opT T -> nat -> State -> T -> State -> Prop :=
  | StepTAS0 : forall tid v,
    xstep TestAndSet tid (mkState v None) false (mkState v (Some tid))
  | StepTAS1 : forall tid tid' v,
    xstep TestAndSet tid (mkState v (Some tid')) true (mkState v (Some tid'))
  | StepClear : forall tid v l,
    xstep Clear tid (mkState v l) tt (mkState v None)
  | StepRead : forall tid v l,
    xstep ReadTAS tid (mkState v l) v (mkState v l)
  | StepWrite : forall tid v0 v l,
    xstep (WriteTAS v) tid (mkState v0 l) tt (mkState v l).

  Definition step := xstep.

  Definition initP s :=
    Lock s = None.

End TASLockAPI.


Module RawLockAPI <: Layer.

  Definition opT := LockOpT.
  Definition State := LockState.

  Inductive xstep : forall T, opT T -> nat -> State -> T -> State -> Prop :=
  | StepAcquire : forall tid v r,
    xstep Acquire tid (mkState v None) r (mkState v (Some tid))
  | StepRelease : forall tid v l,
    xstep Release tid (mkState v l) tt (mkState v None)
  | StepRead : forall tid v l,
    xstep Read tid (mkState v l) v (mkState v l)
  | StepWrite : forall tid v0 v l,
    xstep (Write v) tid (mkState v0 l) tt (mkState v l).

  Definition step := xstep.

  Definition initP s :=
    Lock s = None.

End RawLockAPI.


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
  | StepAcquire : forall tid v r,
    xstep Acquire tid (mkState v None) r (mkState v (Some tid))
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

  Definition initP s :=
    Lock s = None.

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

  Definition initP s :=
    Lock s = None.

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

  Definition initP (s : State) :=
    True.

End CounterAPI.


(** Locking discipline *)

Module LockingRule <: ProcRule LockAPI.

  Definition locked_protocol_op T (op : LockAPI.opT T)
                                (old_owner : bool) (new_owner : bool) :=
    match op with
    | Acquire => new_owner = true
    | Release => old_owner = true /\ new_owner = false
    | Read => old_owner = true /\ new_owner = true
    | Write _ => old_owner = true /\ new_owner = true
    end.

  Definition lock_match s tid :=
    match Lock s with
    | Some tid' =>
      if tid' == tid then true else false
    | None => false
    end.

  Definition follows_protocol ts :=
    forall s,
      follows_protocol_s lock_match locked_protocol_op ts s.

End LockingRule.


(** Using locks to get atomicity. *)

Module LockingCounter <: LayerImplFollowsRule LockAPI LockedCounterAPI LockingRule.

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
      proc_match (Compile.compile_ok compile_op) ts1 ts2 ->
      traces_match_ts LockAPI.step LockedCounterAPI.step ts1 ts2.
  Proof.
    intros.
    eapply Compile.compile_traces_match_ts; eauto.
  Qed.

  Definition absR (s1 : LockAPI.State) (s2 : LockedCounterAPI.State) :=
    s1 = s2.

  Definition compile_ts := Compile.compile_ts compile_op.

  Theorem compile_ts_no_atomics :
    forall ts,
      no_atomics_ts ts ->
      no_atomics_ts (compile_ts ts).
  Proof.
    eapply Compile.compile_ts_no_atomics.
    destruct op; compute; eauto.
  Qed.

  Theorem compile_traces_match :
    forall ts2,
      no_atomics_ts ts2 ->
      traces_match_abs absR LockAPI.initP LockAPI.step LockedCounterAPI.step (compile_ts ts2) ts2.
  Proof.
    unfold traces_match_abs; intros.
    rewrite H2 in *; clear H2.
    eapply all_traces_match; eauto.
    eapply Compile.compile_ts_ok; eauto.
  Qed.

  Hint Constructors follows_protocol_proc.

  Theorem compile_ts_follows_protocol :
    forall ts,
      no_atomics_ts ts ->
      LockingRule.follows_protocol (compile_ts ts).
  Proof.
    unfold compile_ts.
    unfold LockingRule.follows_protocol.
    unfold follows_protocol_s.
    intros.

    pose proof (Compile.compile_ts_ok compile_op H).
    eapply proc_match_pick with (tid := tid) in H1.
    intuition idtac; try congruence.
    repeat deex.
    rewrite H0 in H1; inversion H1; clear H1; subst; repeat sigT_eq.

    clear H2 H0 H ts.
(*
    induction H3.
    - destruct op; simpl; repeat econstructor.
    - eauto.
    - deex.
      admit.
    - deex.
      eexists.
      econstructor.
      econstructor. econstructor. econstructor.
*)
  Admitted.

  Theorem absInitP :
    forall s1 s2,
      LockAPI.initP s1 ->
      absR s1 s2 ->
      LockedCounterAPI.initP s2.
  Proof.
    congruence.
  Qed.

End LockingCounter.


(** Abstracting away the lock details. *)

Module AbsCounter <: LayerImpl LockedCounterAPI CounterAPI.

  Definition absR (s1 : LockedCounterAPI.State) (s2 : CounterAPI.State) :=
    Lock s1 = None /\
    Value s1 = s2.

  Definition compile_ts (ts : @threads_state CounterAPI.opT) := ts.

  Theorem compile_ts_no_atomics :
    forall (ts : @threads_state CounterAPI.opT),
      no_atomics_ts ts ->
      no_atomics_ts (compile_ts ts).
  Proof.
    unfold compile_ts; eauto.
  Qed.

  Theorem absR_ok :
    op_abs absR LockedCounterAPI.step CounterAPI.step.
  Proof.
    unfold op_abs; intros.
    destruct s1; inversion H; clear H.
    simpl in *; subst.
    unfold absR.
    destruct op; inversion H0; clear H0; repeat sigT_eq.
    all: eexists; intuition eauto; constructor.
  Qed.

  Hint Resolve absR_ok.

  Theorem compile_traces_match :
    forall ts,
      no_atomics_ts ts ->
      traces_match_abs absR LockedCounterAPI.initP LockedCounterAPI.step CounterAPI.step (compile_ts ts) ts.
  Proof.
    unfold compile_ts, traces_match_abs; intros.
    eexists; intuition idtac.
    eapply trace_incl_abs; eauto.
    eauto.
  Qed.

  Theorem absInitP :
    forall s1 s2,
      LockedCounterAPI.initP s1 ->
      absR s1 s2 ->
      CounterAPI.initP s2.
  Proof.
    firstorder.
  Qed.

End AbsCounter.


(** Adding ghost state to the test-and-set bit. *)

Module AbsLock <: LayerImpl TASAPI TASLockAPI.

  Definition absR (s1 : TASAPI.State) (s2 : TASLockAPI.State) :=
    TASValue s1 = Value s2 /\
    (TASLock s1 = false /\ Lock s2 = None \/
     exists tid,
     TASLock s1 = true /\ Lock s2 = Some tid).

  Definition compile_ts (ts : @threads_state TASLockAPI.opT) := ts.

  Theorem compile_ts_no_atomics :
    forall (ts : @threads_state TASLockAPI.opT),
      no_atomics_ts ts ->
      no_atomics_ts (compile_ts ts).
  Proof.
    unfold compile_ts; eauto.
  Qed.

  Hint Constructors TASLockAPI.xstep.

  Theorem absR_ok :
    op_abs absR TASAPI.step TASLockAPI.step.
  Proof.
    unfold op_abs; intros.
    destruct s1; destruct s2; unfold absR in *.
    unfold TASLockAPI.step.
    ( intuition idtac ); simpl in *; subst; repeat deex.
    - inversion H0; clear H0; subst; repeat sigT_eq; simpl in *.
      all: eexists; (intuition idtac); [ | | eauto ].
      all: simpl; eauto.
    - inversion H0; clear H0; subst; repeat sigT_eq; simpl in *.
      all: eexists; (intuition idtac); [ | | eauto ].
      all: simpl; eauto.
  Qed.

  Hint Resolve absR_ok.

  Theorem compile_traces_match :
    forall ts,
      no_atomics_ts ts ->
      traces_match_abs absR TASAPI.initP TASAPI.step TASLockAPI.step (compile_ts ts) ts.
  Proof.
    unfold compile_ts, traces_match_abs; intros.
    eexists; intuition idtac.
    eapply trace_incl_abs; eauto.
    eauto.
  Qed.

  Theorem absInitP :
    forall s1 s2,
      TASAPI.initP s1 ->
      absR s1 s2 ->
      TASLockAPI.initP s2.
  Proof.
    unfold absR, TASAPI.initP, TASLockAPI.initP.
    intuition eauto.
    deex; congruence.
  Qed.

End AbsLock.


(** Implement [Acquire] on top of test-and-set *)

Module LockImpl <: LayerImpl TASLockAPI RawLockAPI.

  Definition acquire_cond (r : bool) :=
    if r == false then true else false.

  Definition acquire_core : proc TASLockAPI.opT _ :=
    Until acquire_cond (Op TestAndSet).

  Definition once_cond {T} (r : T) :=
    true.

  Definition release_core : proc TASLockAPI.opT _ :=
    Until once_cond (Op Clear).

  Definition read_core : proc TASLockAPI.opT _ :=
    Until once_cond (Op ReadTAS).

  Definition write_core v : proc TASLockAPI.opT _ :=
    Until once_cond (Op (WriteTAS v)).

  Definition compile_op T (op : RawLockAPI.opT T) : (TASLockAPI.opT T) * (T -> bool) :=
    match op with
    | Acquire => (TestAndSet, acquire_cond)
    | Release => (Clear, once_cond)
    | Read => (ReadTAS, once_cond)
    | Write v => (WriteTAS v, once_cond)
    end.

  Definition compile_ts ts :=
    CompileLoop.compile_ts compile_op ts.

  Theorem compile_ts_no_atomics :
    forall ts,
      no_atomics_ts ts ->
      no_atomics_ts (compile_ts ts).
  Proof.
    eapply CompileLoop.compile_ts_no_atomics.
  Qed.

  Definition absR (s1 : TASLockAPI.State) (s2 : RawLockAPI.State) :=
    s1 = s2.

  Ltac step_inv :=
    match goal with
    | H : TASLockAPI.step _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : RawLockAPI.step _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    end.

  Ltac pair_inv :=
    match goal with
    | H : (_, _) = (_, _) |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    end.

  Hint Constructors RawLockAPI.xstep.

  Theorem noop_or_success :
    noop_or_success compile_op TASLockAPI.step RawLockAPI.step.
  Proof.
    unfold noop_or_success.
    unfold RawLockAPI.step.
    destruct opM; simpl; intros; pair_inv; step_inv; eauto.
  Qed.

  Theorem compile_traces_match :
    forall ts,
      no_atomics_ts ts ->
      traces_match_abs absR TASLockAPI.initP TASLockAPI.step RawLockAPI.step (compile_ts ts) ts.
  Proof.
    unfold traces_match_abs, absR; intros; subst.
    eapply CompileLoop.compile_traces_match_ts; eauto.
    eapply noop_or_success.
    eapply CompileLoop.compile_ts_ok; eauto.
  Qed.

  Theorem absInitP :
    forall s1 s2,
      TASLockAPI.initP s1 ->
      absR s1 s2 ->
      RawLockAPI.initP s2.
  Proof.
    congruence.
  Qed.

End LockImpl.


(** Locking discipline *)

Module LockProtocol <: LayerImplRequiresRule RawLockAPI LockAPI LockingRule.

  Import LockingRule.

  Definition absR (s1 : RawLockAPI.State) (s2 : LockAPI.State) :=
    s1 = s2.

  Ltac step_inv :=
    match goal with
    | H : RawLockAPI.step _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : LockAPI.step _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    end.

  Theorem locked_protocol_step : forall `(op : LockAPI.opT T) tid s v s' b,
    RawLockAPI.step op tid s v s' ->
    locked_protocol_op op (lock_match s tid) b ->
    LockAPI.step op tid s v s'.
  Proof.
    intros.
    destruct s.
    step_inv; unfold lock_match in *; simpl in *.
    - eauto.
    - destruct Lock0; [ destruct (n == tid) | ]; subst; simpl in *;
        intuition eauto; congruence.
    - destruct Lock0; [ destruct (n == tid) | ]; subst; simpl in *;
        intuition eauto; congruence.
    - destruct Lock0; [ destruct (n == tid) | ]; subst; simpl in *;
        intuition eauto; congruence.
  Qed.

  Lemma locked_protocol_owner : forall `(op : RawLockAPI.opT T) tid s v s' b,
    RawLockAPI.step op tid s v s' ->
    locked_protocol_op op (lock_match s tid) b ->
    b = lock_match s' tid.
  Proof.
    intros; step_inv; unfold lock_match in *; simpl in *;
      intuition try congruence.
    destruct (tid == tid); congruence.
  Qed.

  Lemma lock_match_disjoint : forall `(op : RawLockAPI.opT T) tid tid' s s' r b,
    RawLockAPI.step op tid s r s' ->
    locked_protocol_op op (lock_match s tid) b ->
    tid <> tid' ->
    lock_match s tid' = lock_match s' tid'.
  Proof.
    intros.
    step_inv; unfold lock_match in *; simpl in *.
    destruct (tid == tid'); congruence.
    all: destruct l; eauto.
    destruct (n == tid); destruct (n == tid'); subst; intuition congruence.
  Qed.

  Hint Resolve locked_protocol_step.
  Hint Resolve locked_protocol_owner.
  Hint Resolve lock_match_disjoint.


  Definition compile_ts (ts : @threads_state LockAPI.opT) := ts.

  Theorem compile_ts_no_atomics :
    forall ts,
      no_atomics_ts ts ->
      no_atomics_ts (compile_ts ts).
  Proof.
    unfold compile_ts; eauto.
  Qed.

  Theorem compile_traces_match :
    forall ts,
      follows_protocol ts ->
      no_atomics_ts ts ->
      traces_match_abs absR RawLockAPI.initP RawLockAPI.step LockAPI.step (compile_ts ts) ts.
  Proof.
    unfold compile_ts, follows_protocol, absR.
    unfold traces_match_abs; intros; subst.
    clear H0 H1.
    destruct H2.
    specialize (H sm).
    induction H0; eauto.
    specialize (H tid _ p) as Htid.
    intuition idtac; repeat deex.

    edestruct IHexec.
      eapply follows_protocol_s_exec_tid_upd; eauto.

    eexists; intuition idtac.
    eapply ExecPrefixOne.
      eauto.
      eapply follows_protocol_exec_tid; eauto.
      eauto.
    eauto.
  Qed.

  Theorem absInitP :
    forall s1 s2,
      RawLockAPI.initP s1 ->
      absR s1 s2 ->
      LockAPI.initP s2.
  Proof.
    congruence.
  Qed.

End LockProtocol.


(** Linking *)

(* End-to-end stack:

  TASAPI --------------------+---------+
    [ AbsLock ]              |         |
  TASLockAPI                [c1]       |
    [ LockImpl ]             |         |
  RawLockAPI ----------------+----+    |
    [ LockProtocol ]         |    |   [c]
  LockAPI                   [c2]  |    |
    [ LockingCounter ]       |   [c3]  |
  LockedCounterAPI ----------+    |    |
    [ AbsCounter ]                |    |
  CounterAPI ---------------------+----+
 *)

Module c1 := Link TASAPI TASLockAPI RawLockAPI AbsLock LockImpl.
Module c2 := LinkWithRule RawLockAPI LockAPI LockedCounterAPI LockingRule LockProtocol LockingCounter.
Module c3 := Link RawLockAPI LockedCounterAPI CounterAPI c2 AbsCounter.
Module c := Link TASAPI RawLockAPI CounterAPI c1 c3.

Print Assumptions c.compile_traces_match.


Definition test_thread :=
  Until (fun _ => false) (_ <- Op Inc; _ <- Op Dec; Ret tt).

Definition test_threads :=
  repeat (Proc test_thread) 16.

Definition compiled_threads :=
  c.compile_ts test_threads.
