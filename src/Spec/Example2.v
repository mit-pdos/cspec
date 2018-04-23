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

Module TASOp <: Ops.

  Inductive xopT : Type -> Type :=
  | TestAndSet : xopT bool
  | Clear : xopT unit
  | Read : xopT nat
  | Write : nat -> xopT unit.

  Definition opT := xopT.

End TASOp.


Module LockOp <: Ops.

  Inductive xopT : Type -> Type :=
  | Acquire : xopT bool
  | Release : xopT unit
  | Read : xopT nat
  | Write : nat -> xopT unit.

  Definition opT := xopT.

End LockOp.


Module CounterOp <: Ops.

  Inductive xopT : Type -> Type :=
  | Inc : xopT nat
  | Dec : xopT nat.

  Definition opT := xopT.

End CounterOp.


Module TASState <: State.

  Record s := mkTASState {
                  TASValue : nat;
                  TASLock : bool;
                }.

  Definition State := s.
  Definition initP s :=
    TASLock s = false.

End TASState.


Module LockState <: State.

  Record s := mkState {
                  Value : nat;
                  Lock : option nat;
                }.

  Definition State := s.
  Definition initP s :=
    Lock s = None.

End LockState.


Module CounterState <: State.

  Definition State := nat.
  Definition initP (s : State) := True.

End CounterState.


(** Layer definitions *)

Module TASAPI <: Layer TASOp TASState.

  Import TASOp.
  Import TASState.

  Inductive xstep : forall T, opT T -> nat -> State -> T -> State -> list event -> Prop :=
  | StepTAS : forall tid v l,
      xstep TestAndSet tid (mkTASState v l) l (mkTASState v true) nil
  | StepClear : forall tid v l,
      xstep Clear tid (mkTASState v l) tt (mkTASState v false) nil
  | StepRead : forall tid v l,
      xstep Read tid (mkTASState v l) v (mkTASState v l) nil
  | StepWrite : forall tid v0 v l,
      xstep (Write v) tid (mkTASState v0 l) tt (mkTASState v l) nil
  .

  Definition step := xstep.

End TASAPI.


Module TASLockAPI <: Layer TASOp LockState.

  Import TASOp.
  Import LockState.

  Inductive xstep : forall T, opT T -> nat -> State -> T -> State -> list event -> Prop :=
  | StepTAS0 : forall tid v,
      xstep TestAndSet tid (mkState v None) false (mkState v (Some tid)) nil
  | StepTAS1 : forall tid tid' v,
      xstep TestAndSet tid (mkState v (Some tid')) true (mkState v (Some tid')) nil
  | StepClear : forall tid v l,
      xstep Clear tid (mkState v l) tt (mkState v None) nil
  | StepRead : forall tid v l,
      xstep Read tid (mkState v l) v (mkState v l) nil
  | StepWrite : forall tid v0 v l,
      xstep (Write v) tid (mkState v0 l) tt (mkState v l) nil
  .

  Definition step := xstep.

End TASLockAPI.


Module RawLockAPI <: Layer LockOp LockState.

  Import LockOp.
  Import LockState.

  Inductive xstep : forall T, opT T -> nat -> State -> T -> State -> list event -> Prop :=
  | StepAcquire : forall tid v r,
      xstep Acquire tid (mkState v None) r (mkState v (Some tid)) nil
  | StepRelease : forall tid v l,
      xstep Release tid (mkState v l) tt (mkState v None) nil
  | StepRead : forall tid v l,
      xstep Read tid (mkState v l) v (mkState v l) nil
  | StepWrite : forall tid v0 v l,
      xstep (Write v) tid (mkState v0 l) tt (mkState v l) nil
  .

  Definition step := xstep.

End RawLockAPI.


Module LockProtocol <: Protocol LockOp LockState.

  Import LockOp.
  Import LockState.

  Inductive xstep_allow : forall T, opT T -> nat -> State -> Prop :=
  | StepAcquire : forall tid s,
      xstep_allow Acquire tid s
  | StepRelease : forall tid v,
      xstep_allow Release tid (mkState v (Some tid))
  | StepRead : forall tid v,
      xstep_allow Read tid (mkState v (Some tid))
  | StepWrite : forall tid v0 v,
      xstep_allow (Write v) tid (mkState v0 (Some tid)).

  Definition step_allow := xstep_allow.

End LockProtocol.


Module LockAPI <: Layer LockOp LockState.

  Definition step_allow := LockProtocol.step_allow.
  Definition step :=
    nilpotent_step RawLockAPI.step step_allow.

End LockAPI.


Module LockedCounterAPI <: Layer CounterOp LockState.

  Import CounterOp.
  Import LockState.

  Inductive xstep : forall T, opT T -> nat -> State -> T -> State -> list event -> Prop :=
  | StepInc : forall tid v,
      xstep Inc tid (mkState v None) v (mkState (v + 1) None) nil
  | StepDec : forall tid v,
      xstep Dec tid (mkState v None) v (mkState (v - 1) None) nil.

  Definition step := xstep.

End LockedCounterAPI.


Module CounterAPI <: Layer CounterOp CounterState.

  Import CounterOp.
  Import CounterState.

  Inductive xstep : forall T, opT T -> nat -> State -> T -> State -> list event -> Prop :=
  | StepInc : forall tid v,
      xstep Inc tid v v (v + 1) nil
  | StepDec : forall tid v,
      xstep Dec tid v v (v - 1) nil.

  Definition step := xstep.

End CounterAPI.


(** Using locks to get atomicity. *)

Module LockingCounter' <:
  LayerImplMoversProtocolT
    LockState
    LockOp    RawLockAPI LockAPI
    CounterOp LockedCounterAPI
    LockProtocol.

  Import LockOp.
  Import CounterOp.

  Definition inc_core : proc LockOp.opT _ :=
    _ <- Op Acquire;
      v <- Op Read;
      _ <- Op (Write (v + 1));
      _ <- Op Release;
      Ret v.

  Definition dec_core : proc LockOp.opT _ :=
    _ <- Op Acquire;
      v <- Op Read;
      _ <- Op (Write (v - 1));
      _ <- Op Release;
      Ret v.

  Definition compile_op T (op : CounterOp.opT T)
    : proc LockOp.opT T :=
    match op with
    | Inc => inc_core
    | Dec => dec_core
    end.

  Theorem compile_op_no_atomics : forall T (op : CounterOp.opT T),
      no_atomics (compile_op op).
  Proof.
    destruct op; econstructor; eauto.
  Qed.


  Ltac step_inv :=
    match goal with
    | H : LockAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : LockAPI.step_allow _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : LockAPI.step_allow _ _ _ -> False |- _ =>
      solve [ exfalso; eauto ]
    | H : RawLockAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : LockedCounterAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    end; intuition idtac.

  Hint Extern 1 (RawLockAPI.step _ _ _ _ _ _) => econstructor.
  Hint Extern 1 (LockAPI.step _ _ _ _ _ _) => left.
  Hint Extern 1 (LockAPI.step _ _ _ _ _ _) => right.
  Hint Extern 1 (LockAPI.step_allow _ _ _) => econstructor.
  Hint Extern 1 (LockedCounterAPI.step _ _ _ _ _ _) => econstructor.
  Hint Extern 1 (~ LockAPI.step_allow _ _ _) => intro H'; inversion H'.
  Hint Extern 1 (LockAPI.step_allow _ _ _ -> False) => intro H'; inversion H'.

  Lemma acquire_right_mover :
    right_mover LockAPI.step Acquire.
  Proof.
    unfold right_mover; intros.
    repeat step_inv; try congruence; eauto;
      try solve [ exfalso; eauto ].

    destruct op1; repeat step_inv; eauto 10;
      try solve [ exfalso; eauto ].
  Qed.

  Lemma release_left_mover :
    left_mover LockAPI.step Release.
  Proof.
    split.
    - eapply always_enabled_to_stable.
      unfold always_enabled, enabled_in; intros.
      destruct s. destruct Lock. destruct (n == tid); subst.
      all: eauto 10.
    - unfold left_mover; intros.
      repeat step_inv; try congruence; subst; eauto 10.
      destruct op0; eauto 10.
      Unshelve.
      all: exact tt.
  Qed.

  Lemma read_right_mover :
    right_mover LockAPI.step Read.
  Proof.
    unfold right_mover; intros.
    repeat step_inv; try congruence; subst; eauto 10.
  Qed.

  Lemma write_right_mover : forall v,
      right_mover LockAPI.step (Write v).
  Proof.
    unfold right_mover; intros.
    repeat step_inv; try congruence; subst; eauto 10.
    destruct op1; eauto 10.
  Qed.

  Hint Resolve acquire_right_mover.
  Hint Resolve release_left_mover.
  Hint Resolve read_right_mover.
  Hint Resolve write_right_mover.

  Theorem ysa_movers : forall T (op : CounterOp.opT T),
      ysa_movers LockAPI.step (compile_op op).
  Proof.
    destruct op; unfold ysa_movers; simpl.
    - unfold inc_core; eauto 20.
    - unfold dec_core; eauto 20.
  Qed.

  Theorem compile_correct :
    compile_correct compile_op LockAPI.step LockedCounterAPI.step.
  Proof.
    unfold compile_correct; intros.
    destruct op.

    + repeat atomic_exec_inv.
      simpl; intuition eauto.
      repeat step_inv; eauto.

    + repeat atomic_exec_inv.
      simpl; intuition eauto.
      repeat step_inv; eauto.
  Qed.


  Import LockState.

  Theorem exec_others_preserves_lock :
    forall tid s s',
      exec_others (restricted_step RawLockAPI.step LockAPI.step_allow) tid s s' ->
      Lock s = Some tid ->
      Lock s' = Some tid.
  Proof.
    induction 1; intros; eauto.
    repeat deex.
    clear H0.
    assert (Lock x = Lock y).
    {
      clear IHclos_refl_trans_1n.
      unfold restricted_step in *; intuition idtac;
        repeat step_inv; simpl in *; congruence.
    }
    rewrite IHclos_refl_trans_1n; congruence.
  Qed.

  Ltac exec_propagate :=
    match goal with
    | s : LockState.State |- _ =>
      destruct s
    | H : exec_any _ _ _ (Op _) _ _ |- _ =>
      eapply exec_any_op in H; repeat deex
    | H : exec_others _ _ _ _ |- _ =>
      eapply exec_others_preserves_lock in H; simpl in *; subst; [ | congruence ]
    end.

  Lemma inc_follows_protocol : forall tid s,
      follows_protocol_proc RawLockAPI.step LockAPI.step_allow tid s inc_core.
  Proof.
    intros.
    constructor; intros.
    constructor; intros. eauto.

    repeat exec_propagate.
    unfold restricted_step in *; intuition idtac; repeat step_inv.
    constructor; intros.
    constructor; intros. eauto.

    repeat exec_propagate.
    unfold restricted_step in *; intuition idtac; repeat step_inv.
    constructor; intros.
    constructor; intros. eauto.

    repeat exec_propagate.
    unfold restricted_step in *; intuition idtac; repeat step_inv.
    constructor; intros.
    constructor; intros. eauto.

    repeat exec_propagate.
    unfold restricted_step in *; intuition idtac; repeat step_inv.
    constructor; intros.
  Qed.

  Lemma dec_follows_protocol : forall tid s,
      follows_protocol_proc RawLockAPI.step LockAPI.step_allow tid s dec_core.
  Proof.
    intros.
    constructor; intros.
    constructor; intros. eauto.

    repeat exec_propagate.
    unfold restricted_step in *; intuition idtac; repeat step_inv.
    constructor; intros.
    constructor; intros. eauto.

    repeat exec_propagate.
    unfold restricted_step in *; intuition idtac; repeat step_inv.
    constructor; intros.
    constructor; intros. eauto.

    repeat exec_propagate.
    unfold restricted_step in *; intuition idtac; repeat step_inv.
    constructor; intros.
    constructor; intros. eauto.

    repeat exec_propagate.
    unfold restricted_step in *; intuition idtac; repeat step_inv.
    constructor; intros.
  Qed.

  Hint Resolve inc_follows_protocol.
  Hint Resolve dec_follows_protocol.

  Theorem op_follows_protocol : forall tid s `(op : CounterOp.opT T),
      follows_protocol_proc RawLockAPI.step LockProtocol.step_allow tid s (compile_op op).
  Proof.
    destruct op; eauto.
  Qed.

  Theorem allowed_stable :
    forall `(op : LockOp.opT T) `(op' : LockOp.opT T') tid tid' s s' r evs,
      tid <> tid' ->
      LockAPI.step_allow op tid s ->
      LockAPI.step op' tid' s r s' evs ->
      LockAPI.step_allow op tid s'.
  Proof.
    intros.
    destruct op; destruct op'; repeat step_inv; subst; eauto.
  Qed.

  Theorem raw_step_ok :
    forall `(op : _ T) tid s r s' evs,
      restricted_step RawLockAPI.step LockProtocol.step_allow op tid s r s' evs ->
      LockAPI.step op tid s r s' evs.
  Proof.
    eauto.
  Qed.

End LockingCounter'.


(** Abstracting away the lock details. *)

Module AbsCounter' <:
  LayerImplAbsT CounterOp
                LockState    LockedCounterAPI
                CounterState CounterAPI.

  Import LockState.

  Definition absR (s1 : LockState.State) (s2 : CounterState.State) :=
    Lock s1 = None /\
    Value s1 = s2.

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

  Theorem absInitP :
    forall s1 s2,
      LockState.initP s1 ->
      absR s1 s2 ->
      CounterState.initP s2.
  Proof.
    firstorder.
  Qed.

End AbsCounter'.

Module AbsCounter :=
  LayerImplAbs CounterOp
               LockState    LockedCounterAPI
               CounterState CounterAPI
               AbsCounter'.


(** Adding ghost state to the test-and-set bit. *)

Module AbsLock' <:
  LayerImplAbsT TASOp
                TASState TASAPI
                LockState TASLockAPI.

  Import TASState.
  Import LockState.

  Definition absR (s1 : TASState.State) (s2 : LockState.State) :=
    TASValue s1 = Value s2 /\
    ((TASLock s1 = false /\ Lock s2 = None) \/
     (exists tid, TASLock s1 = true /\ Lock s2 = Some tid)).

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

  Theorem absInitP :
    forall s1 s2,
      TASState.initP s1 ->
      absR s1 s2 ->
      LockState.initP s2.
  Proof.
    unfold absR, TASState.initP, LockState.initP.
    intuition eauto.
    deex; congruence.
  Qed.

End AbsLock'.

Module AbsLock :=
  LayerImplAbs TASOp
               TASState TASAPI
               LockState TASLockAPI
               AbsLock'.


(** Implement [Acquire] on top of test-and-set *)

Module LockImpl' <:
  LayerImplLoopT
    LockState
    TASOp  TASLockAPI
    LockOp RawLockAPI.

  Definition acquire_cond (r : bool) :=
    if r == false then true else false.

  Definition once_cond {T} (r : T) :=
    true.

  Import TASOp.
  Import LockOp.

  Definition compile_op T (op : LockOp.opT T) : (option T -> TASOp.opT T) * (T -> bool) * option T :=
    match op with
    | Acquire => (fun _ => TestAndSet, acquire_cond, None)
    | Release => (fun _ => Clear, once_cond, None)
    | Read => (fun _ => TASOp.Read, once_cond, None)
    | Write v => (fun _ => TASOp.Write v, once_cond, None)
    end.

  Ltac step_inv :=
    match goal with
    | H : TASLockAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : RawLockAPI.step _ _ _ _ _ _ |- _ =>
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

End LockImpl'.

Module LockImpl :=
  LayerImplLoop
    LockState
    TASOp  TASLockAPI
    LockOp RawLockAPI
    LockImpl'.


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

Module c1 :=
  Link
    TASOp  TASState  TASAPI
    TASOp  LockState TASLockAPI
    LockOp LockState RawLockAPI
    AbsLock LockImpl.
Module c2 :=
  LayerImplMoversProtocol
    LockState
    LockOp    RawLockAPI LockAPI
    CounterOp LockedCounterAPI
    LockProtocol
    LockingCounter'.
Module c3 :=
  Link
    LockOp    LockState    RawLockAPI
    CounterOp LockState    LockedCounterAPI
    CounterOp CounterState CounterAPI
    c2 AbsCounter.
Module c :=
  Link
    TASOp     TASState     TASAPI
    LockOp    LockState    RawLockAPI
    CounterOp CounterState CounterAPI
    c1 c3.

Print Assumptions c.compile_traces_match.


Import CounterOp.

Definition test_thread :=
  Until
    (fun _ => false)
    (fun _ => _ <- Op Inc; _ <- Op Dec; Ret tt)
    None.

Definition test_threads :=
  repeat (Proc test_thread) 16.

Definition compiled_threads :=
  c.compile_ts test_threads.
