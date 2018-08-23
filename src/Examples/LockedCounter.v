Require Import CSPEC.
Require Import Helpers.Learn.
Require Import TSO.

Import ListNotations.

Global Set Implicit Arguments.
Global Generalizable All Variables.

Module TSOOp <: Ops.

  Inductive addr := addr0 | addr1.
  Global Instance addr_equal_dec : EqualDec addr := ltac:(hnf; decide equality).

  Definition Val := TSOOp.addr0.
  Definition Lock := TSOOp.addr1.
  Definition cLocked := 1.
  (* this is the canonical unlocked value, but any value but cLocked will do *)
  Definition cUnlocked := 0.

  Inductive xOp : Type -> Type :=
  | Read : addr -> xOp nat
  | Write : addr -> nat -> xOp unit
  | TestAndSet : addr -> nat -> xOp nat
  (* this is specifically an MFENCE *)
  | Fence : xOp unit
  .

  Definition Op := xOp.

End TSOOp.

Module TSOState <: State.

  Definition State := memT TSOOp.addr nat.

  Definition initP (s:State) :=
    s = {| MemValue := fun a => TSOOp.cUnlocked; SBuf := fun _ => [] |}.

End TSOState.

Definition bg_step `(step: OpSemantics Op State) (bg: State -> State -> Prop) : OpSemantics Op State :=
  fun _ op tid s r s' evs =>
    exists s0 s1, bg s0 s /\
          step _ op tid s r s1 evs /\
          bg s1 s'.

Module TSOAPI <: Layer TSOOp TSOState.
  Import TSOOp.
  Import TSOState.

  Inductive xstep : forall T, Op T -> nat -> State -> T -> State -> list event -> Prop :=
  | StepRead : forall tid a s,
      xstep (Read a) tid s (mem_read s a tid) s nil
  | StepWrite : forall tid a v s,
      xstep (Write a v) tid s tt (mem_write a v s tid) nil
  | StepTestAndSet : forall tid a v s,
      xstep (TestAndSet a v) tid
            s
            (mem_read s a tid)
            (mem_flush (mem_write a v s tid) tid) nil
  | StepFence : forall tid s,
      xstep Fence tid s tt (mem_flush s tid) nil
  .

  Definition step := bg_step xstep mem_bg.

End TSOAPI.

Module TSODelayNondetAPI <: Layer TSOOp TSOState.
  Import TSOOp TSOState.

  Inductive xstep : forall T, Op T -> nat -> State -> T -> State -> list event -> Prop :=
  | StepRead : forall tid a s s',
      mem_bg s s' ->
      xstep (Read a) tid s (mem_read s' a tid) s' nil
  | StepWrite : forall tid a v s,
      xstep (Write a v) tid s tt (mem_write a v s tid) nil
  | StepTestAndSet : forall tid a v s s',
      mem_bg s s' ->
      xstep (TestAndSet a v) tid
            s
            (mem_read s' a tid)
            (mem_flush (mem_write a v s' tid) tid) nil
  | StepFence : forall tid s s',
      mem_bg s s' ->
      xstep Fence tid s tt (mem_flush s' tid) nil
  .

  Definition step := xstep.

End TSODelayNondetAPI.

(** IMPL: TSODelayNondetAPI -> TSOAPI *)

Module AbsNondet' <:
  LayerImplAbsT TSOOp
                TSOState TSOAPI
                TSOState TSODelayNondetAPI.

  Import TSOState.

  (* absR is from low (full nondeterminism) to high (careful nondeterminism) *)
  Definition absR (s1 : State) (s2 : State) :=
    mem_bg s2 s1.

  Hint Resolve mem_bg_commute_write.
  Hint Constructors TSODelayNondetAPI.xstep.

  Theorem absR_ok :
    op_abs absR TSOAPI.step TSODelayNondetAPI.step.
  Proof.
    unfold op_abs, TSODelayNondetAPI.step; intros.
    unfold absR in *.
    hnf in H0; repeat deex.
    destruct op; inv_clear H1; eauto.
    descend; split; [ | eauto ]; eauto.
  Qed.

  Theorem absInitP :
    forall s1,
      TSOState.initP s1 ->
      exists s2, absR s1 s2 /\
            TSOState.initP s2.
  Proof.
    unfold initP, absR; intros.
    destruct s1; propositional.
    invert H; clear H.
    exists_econstructor; intuition eauto.
    reflexivity.
  Qed.

End AbsNondet'.

Module AbsNondet :=
  LayerImplAbs TSOOp
               TSOState TSOAPI
               TSOState TSODelayNondetAPI
               AbsNondet'.

(** LAYER: TASAPI *)

Module TASOp <: Ops.

  Inductive xOp : Type -> Type :=
  | TryAcquire : xOp bool (* true if acquired *)
  | Clear : xOp unit
  | Read : xOp nat
  | Write : nat -> xOp unit
  (* we won't actually use a fence *)
  (* | Flush : xOp unit *)
  .

  Definition Op := xOp.

End TASOp.

Module TAS_TSOAPI <: Layer TASOp TSOState.
  Import TSOOp.
  Import TASOp.
  Import TSOState.

  Inductive xstep : forall T, Op T -> nat -> State -> T -> State -> list event -> Prop :=
  | StepTryAcquireSuccess : forall tid s s',
      mem_bg s s' ->
      mem_read s' Lock tid <> cLocked ->
      xstep TryAcquire tid
            s
            true
            (mem_flush (mem_write Lock cLocked s' tid) tid) nil
  | StepTryAcquireFail : forall tid s s',
      mem_bg s s' ->
      xstep TryAcquire tid
            s
            false
            (mem_flush s' tid)
            nil
  | StepClear : forall tid s,
      xstep Clear tid s tt (mem_write Lock cUnlocked s tid) nil
  | StepRead : forall tid s s',
      mem_bg s s' ->
      xstep Read tid s (mem_read s' Val tid) s' nil
  | StepWrite : forall tid s v,
      xstep (Write v) tid s tt (mem_write Val v s tid) nil
  (* | StepFlush : forall tid s s',
      mem_bg s s' ->
      xstep Flush tid s tt (mem_flush s' tid) nil. *)
  .

  Definition step := xstep.

End TAS_TSOAPI.

Module TAS_TSOImpl <: LayerImplMoversT
                        TSOState
                        TSOOp TSODelayNondetAPI
                        TASOp TAS_TSOAPI.
  Import TSOOp.
  Import TSODelayNondetAPI.

  Definition compile_op T (o: TASOp.Op T) : proc Op T :=
    match o with
    | TASOp.TryAcquire => l <- Call (TestAndSet Lock cLocked);
                           (* need to report true if lock was acquired *)
                           Ret (if l == cLocked then false else true)
    | TASOp.Clear => Call (Write Lock cUnlocked)
    | TASOp.Read => Call (Read Val)
    | TASOp.Write v => Call (Write Val v)
    (* | TASOp.Flush => Call (Fence) *)
    end.

  Theorem compile_op_no_atomics : forall T (op: TASOp.Op T),
      no_atomics (compile_op op).
  Proof.
    destruct op; simpl; eauto using no_atomics.
  Qed.

  Hint Constructors xstep.

  Theorem ysa_movers :
    forall (T : Type) (op : TASOp.Op T),
      ysa_movers step (compile_op op).
  Proof.
    destruct op; simpl; eauto.
  Qed.

  Hint Constructors TAS_TSOAPI.xstep.

  Theorem compile_correct :
    compile_correct compile_op step TAS_TSOAPI.step.
  Proof.
    unfold TAS_TSOAPI.step.
    hnf; intros.
    destruct op; simpl in *;
      repeat match goal with
             | [ H: atomic_exec _ _ _ _ _ _ _ |- _ ] =>
               invert H; clear H
             | [ H: step _ _ _ _ _ _ |- _ ] =>
               invert H; clear H
             end;
      simpl; eauto.

    destruct (mem_read s'0 Lock tid == cLocked).
    rewrite mem_write_flush_same; auto.
    constructor; eauto.
  Qed.

End TAS_TSOImpl.

Module LockOwnerState <: State.

  Record s := mkLOState {
                  TASValue : memT TSOOp.addr nat;
                  TASLock : option nat;
                }.
  Definition State := s.

  Definition initP s :=
    TASValue s = {| MemValue := fun _ => 0; SBuf := fun _ => [] |} /\
    TASLock s = None.
End LockOwnerState.


Module LockOwnerAPI <: Layer TASOp LockOwnerState.

  Import TSOOp.
  Import TASOp.
  Import LockOwnerState.

  Inductive xstep : forall T, Op T -> nat -> State -> T -> State -> list event -> Prop :=
  | StepTryAcquireSuccess : forall tid s s' l,
      mem_bg s s' ->
      xstep TryAcquire tid
            (mkLOState s l)
            true
            (mkLOState (mem_flush (mem_write Lock cLocked s' tid) tid) (Some tid))
            nil
  | StepTryAcquireFail : forall tid s l s',
      mem_bg s s' ->
      xstep TryAcquire tid
            (mkLOState s l)
            false
            (mkLOState (mem_flush s' tid) None)
            nil
  | StepClear : forall tid s l,
      xstep Clear tid (mkLOState s l)
            tt
            (mkLOState (mem_write Lock cUnlocked s tid) l)
            nil
  | StepRead : forall tid s s' l,
      mem_bg s s' ->
      xstep Read tid
            (mkLOState s l)
            (mem_read s' Val tid)
            (mkLOState s' l)
            nil
  | StepWrite : forall tid s v l,
      xstep (Write v) tid
            (mkLOState s l)
            tt
            (mkLOState (mem_write Val v s tid) l)
            nil
  (* | StepFlush : forall tid s s' l,
      mem_bg s s' ->
      xstep Flush tid
            (mkLOState s l)
            tt
            (mkLOState (mem_flush s' tid) l)
            nil *)
  .

  Definition step := xstep.

End LockOwnerAPI.


Module AbsLockOwner' <: LayerImplAbsT
                          TASOp
                          TSOState TAS_TSOAPI
                          LockOwnerState LockOwnerAPI.
  Import TSOOp.
  Import TASOp.
  Import TSOState LockOwnerState.

  Definition absR (s1: TSOState.State) (s2: State) :=
    s2.(TASValue) = s1.

  Lemma absR_unfold : forall s1 s l,
      s = s1 ->
      absR s1 (mkLOState s l).
  Proof.
    unfold absR; propositional; intuition auto.
  Qed.

  Import LockOwnerAPI.

  Hint Resolve absR_unfold.
  Hint Constructors xstep.

  Theorem absR_ok : op_abs absR TAS_TSOAPI.step step.
  Proof.
    unfold step.
    hnf; intros.
    destruct s2; unfold absR in * |- ; simpl in *; propositional.
    invert H0; clear H0;
      try solve [ exists_econstructor; eauto ].
  Qed.

  Theorem absInitP :
    forall s1,
      TSOState.initP s1 ->
      exists s2 : State, absR s1 s2 /\ initP s2.
  Proof.
    unfold TSOState.initP, initP; propositional.
    exists_econstructor; eauto.
  Qed.

End AbsLockOwner'.

Module AbsLockOwner :=
  LayerImplAbs TASOp
               TSOState TAS_TSOAPI
               LockOwnerState LockOwnerAPI
               AbsLockOwner'.

Module TASState <: State.

  Record s := mkTASState {
                  TASValue : memT unit nat;
                  TASLock : option nat;
                }.

  Definition State := s.
  Definition initP s :=
    TASLock s = None /\
    TASValue s = {| MemValue := fun _ => 0; SBuf := fun _ => [] |}.

End TASState.

(** LAYER: TASAPI *)

Module TASAPI <: Layer TASOp TASState.

  Import TASOp.
  Import TASState.

  Inductive xstep : forall T, Op T -> nat -> State -> T -> State -> list event -> Prop :=
  | StepTryAcquireSuccess : forall tid v,
      xstep TryAcquire tid (mkTASState v None) true (mkTASState v (Some tid)) nil
  | StepTryAcquireFail : forall tid v l,
      (* the lock is freed when the release is in the store buffer, but you
      might still not acquire the lock if you don't see the release *)
      xstep TryAcquire tid (mkTASState v l) false (mkTASState v l) nil
  | StepClear : forall tid v l,
      xstep Clear tid (mkTASState v l) tt (mkTASState v None) nil
  | StepRead : forall tid v v' l,
      mem_bg v v' ->
      xstep Read tid (mkTASState v l) (mem_read v' tt tid) (mkTASState v' l) nil
  | StepWrite : forall tid v0 v l,
      xstep (Write v) tid (mkTASState v0 l) tt (mkTASState (mem_write tt v v0 tid) l) nil
  | StepFlush : forall tid v v' l,
      mem_bg v v' ->
      xstep Flush tid (mkTASState v l) tt (mkTASState (mem_flush v' tid) l) nil
  .

  Definition step := xstep.

End TASAPI.

(** IMPL: TSO_TASAPI -> TASAPI *)

Module AbsTSO' <: LayerImplAbsT
                    TASOp
                    TSOState TAS_TSOAPI
                    TASState TASAPI.

  Import TSOOp.
  Import TSOState TASState.

  Fixpoint filter_writes (ws: list (addr*nat)) : list (unit*nat) :=
    match ws with
    | nil => nil
    | (a,v)::ws' => if a == Val
                   then (tt,v)::filter_writes ws'
                   else filter_writes ws'
    end.

  Definition Forall_writes (a:addr) (P: nat -> Prop) : list (addr*nat) -> Prop :=
    List.Forall (fun '(a', v) => a = a' -> P v).

  Definition absR (s2: TSOState.State) (s1: State) :=
    (forall tid, s1.(TASValue).(SBuf) tid = filter_writes (s2.(SBuf) tid)) /\
    (* if the lock is supposedly held, it must be visibile to everyone *)
    (forall tid, s1.(TASLock) = Some tid ->
            forall tid', mem_read s2 Lock tid' = cLocked /\
                    Forall_writes Lock (fun _ => False) (s2.(SBuf) tid)) /\
    (forall tid, mem_read s2 Lock tid = cLocked ->
            s1.(TASLock) <> None) /\
    (* if you find the lock unheld, you're never being lied to *)
    (forall tid, mem_read s2 Lock tid <> cLocked ->
            s1.(TASLock) = None).

  Import TASAPI.

  Theorem absR_stable {s1 s1' s2} :
      absR s1 s2 ->
      mem_bg s1 s1' ->
      absR s1' s2.
  Proof.
  Admitted.

  Theorem absR_unlocked {s1 s2 tid} :
      absR s1 s2 ->
      mem_read s1 Lock tid <> cLocked ->
      s2.(TASLock) = None.
  Proof.
  Admitted.

  Theorem absR_preserved_lock : forall s1 tid v,
      absR s1 {| TASValue := v; TASLock := None |} ->
      absR (mem_flush (mem_write Lock cLocked s1 tid) tid)
           {| TASValue := v; TASLock := Some tid |}.
  Admitted.

  Ltac absR :=
    repeat match goal with
           | [ H: absR ?s _,
                  H': mem_bg ?s ?s' |- _ ] =>
             pose proof (absR_stable H H');
             clear H H';
             try clear s
           | [ H: absR ?s _,
                  H': mem_read ?s Lock _ <> cLocked |- _ ] =>
             apply (absR_unlocked H) in H';
             simpl in H';
             subst
           end.

  Theorem absR_ok : op_abs absR TAS_TSOAPI.step step.
  Proof.
    unfold step.
    hnf; intros.
    cut (exists s2', xstep op tid s2 r s2' evs /\ absR s1' s2');
      [ now (propositional; eauto) | ].
    destruct op.
    - invert H0; clear H0; absR.
      + destruct s2; simpl in *; propositional.
        exists_econstructor; split.
        econstructor.
        eapply absR_preserved_lock; eauto.
      + destruct s2.
        exists_econstructor; split.
        econstructor.


  Admitted.

  Theorem absInitP :
    forall s1 : TSOState.State,
      TSOState.initP s1 -> exists s2 : State, absR s1 s2 /\ initP s2.
  Proof.
    unfold TSOState.initP, initP, absR; propositional.
    exists (mkTASState (mkMem (fun _ => cUnlocked) (fun _ => [])) None);
      simpl;
      (intuition auto);
      try congruence.
    unfold mem_read in H; simpl in *.
    invert H.
  Qed.

End AbsTSO'.


(** LAYER: TASLockAPI *)

Module LockOp <: Ops.

  Inductive xOp : Type -> Type :=
  | Acquire : xOp bool
  | Release : xOp unit
  | Read : xOp nat
  | Write : nat -> xOp unit
  | Flush : xOp unit.

  Definition Op := xOp.

End LockOp.

Module LockState <: State.

  Record s := mkState {
                  Value : memT unit nat;
                  Lock : option nat;
                }.

  Definition State := s.
  Definition initP s :=
    Lock s = None /\
    Value s = {| MemValue := fun _ => 0; SBuf := fun _ => [] |}.

End LockState.

Module TASLockAPI <: Layer TASOp LockState.

  Import TASOp.
  Import LockState.

  Inductive xstep : forall T, Op T -> nat -> State -> T -> State -> list event -> Prop :=
  | StepTAS0 : forall tid v,
      xstep TestAndSet tid (mkState v None) false (mkState v (Some tid)) nil
  | StepTAS1 : forall tid tid' v,
      xstep TestAndSet tid (mkState v (Some tid')) true (mkState v (Some tid')) nil
  | StepClear : forall tid v l,
      xstep Clear tid (mkState v l) tt (mkState v None) nil
  | StepRead : forall tid v v' l,
      mem_bg v v' ->
      xstep Read tid (mkState v l) (mem_read v' tt tid) (mkState v' l) nil
  | StepWrite : forall tid v0 v l,
      xstep (Write v) tid (mkState v0 l) tt (mkState (mem_write tt v v0 tid) l) nil
  | StepFlush : forall tid v v' l,
      mem_bg v v' ->
      xstep Flush tid (mkState v l) tt (mkState (mem_flush v' tid) l) nil
  .

  Definition step := xstep.

End TASLockAPI.

(** IMPL: TASLockAPI -> TASAPI

Adding ghost state to the test-and-set bit. *)

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
    forall s1,
      TASState.initP s1 ->
      exists s2, absR s1 s2 /\
      LockState.initP s2.
  Proof.
    unfold absR, TASState.initP, LockState.initP; intros.
    exists_econstructor; intuition eauto.
  Qed.

End AbsLock'.

Module AbsLock :=
  LayerImplAbs TASOp
               TASState TASAPI
               LockState TASLockAPI
               AbsLock'.

(** LAYER: RawLockAPI *)

Module RawLockAPI <: Layer LockOp LockState.

  Import LockOp.
  Import LockState.

  Inductive xstep : forall T, Op T -> nat -> State -> T -> State -> list event -> Prop :=
  | StepAcquire : forall tid v r,
      xstep Acquire tid (mkState v None) r (mkState v (Some tid)) nil
  | StepRelease : forall tid v l,
      xstep Release tid (mkState v l) tt (mkState v None) nil
  | StepRead : forall tid v v' l,
      mem_bg v v' ->
      xstep Read tid (mkState v l) (mem_read v' tt tid) (mkState v' l) nil
  | StepWrite : forall tid v0 v l,
      xstep (Write v) tid (mkState v0 l) tt (mkState (mem_write tt v v0 tid) l) nil
  | StepFlush : forall tid v v' l,
      mem_bg v v' ->
      xstep Flush tid (mkState v l) tt (mkState (mem_flush v' tid) l) nil
  .

  Definition step := xstep.

End RawLockAPI.

Module LockProtocol <: Protocol LockOp LockState.

  Import LockOp.
  Import LockState.

  Inductive xstep_allow : forall T, Op T -> nat -> State -> Prop :=
  | StepAcquire : forall tid s,
      xstep_allow Acquire tid s
  | StepRelease : forall tid v,
      xstep_allow Release tid (mkState v (Some tid))
  | StepRead : forall tid v,
      xstep_allow Read tid (mkState v (Some tid))
  | StepWrite : forall tid v0 v,
      xstep_allow (Write v) tid (mkState v0 (Some tid))
  | StepFlush : forall tid v,
      xstep_allow Flush tid (mkState v (Some tid))
  .

  Definition step_allow := xstep_allow.

End LockProtocol.


Module LockAPI <: Layer LockOp LockState.

  Definition step_allow := LockProtocol.step_allow.
  Definition step :=
    nilpotent_step RawLockAPI.step step_allow.

End LockAPI.

(** LAYER: LockedCounterAPI *)

Module CounterOp <: Ops.

  Inductive xOp : Type -> Type :=
  | Inc : xOp nat
  | Dec : xOp nat.

  Definition Op := xOp.

End CounterOp.


Module LockedCounterAPI <: Layer CounterOp LockState.

  Import CounterOp.
  Import LockState.

  Inductive xstep : forall T, Op T -> nat -> State -> T -> State -> list event -> Prop :=
  | StepInc : forall (tid: nat) v0 v v' r,
      mem_bg v0 v ->
      r = mem_read v tt tid ->
      mem_bg (mem_write tt (mem_read v tt tid + 1) v tid) v' ->
      xstep Inc tid (mkState v0 None) r
            (mkState (mem_flush v' tid) None) nil
  | StepDec : forall (tid: nat) v0 v v' r,
      mem_bg v0 v ->
      r = mem_read v tt tid ->
      mem_bg (mem_write tt (mem_read v tt tid - 1) v tid) v' ->
      xstep Dec tid (mkState v0 None) r
            (mkState (mem_flush v' tid) None) nil.

  Definition step := xstep.

End LockedCounterAPI.

(** Using locks to get atomicity. *)

Module LockingCounter' <:
  LayerImplMoversProtocolT
    LockState
    LockOp    RawLockAPI LockAPI
    CounterOp LockedCounterAPI
    LockProtocol.

  Import LockOp.
  Import CounterOp.

  Definition inc_core : proc LockOp.Op _ :=
    _ <- Call Acquire;
      v <- Call Read;
      _ <- Call (Write (v + 1));
      _ <- Call Flush;
      _ <- Call Release;
      Ret v.

  Definition dec_core : proc LockOp.Op _ :=
    _ <- Call Acquire;
      v <- Call Read;
      _ <- Call (Write (v - 1));
      _ <- Call Flush;
      _ <- Call Release;
      Ret v.

  Definition compile_op T (op : CounterOp.Op T)
    : proc LockOp.Op T :=
    match op with
    | Inc => inc_core
    | Dec => dec_core
    end.

  Theorem compile_op_no_atomics : forall T (op : CounterOp.Op T),
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
    repeat step_inv; eauto 10.
    destruct op1; repeat step_inv; eauto 10.
  Qed.

  Lemma flush_right_mover :
    right_mover LockAPI.step Flush.
  Proof.
    unfold right_mover; intros.
    repeat step_inv; eauto 15.
    destruct op1; repeat step_inv; eauto 15.
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
      repeat step_inv; subst; eauto 15.
      destruct op0; eauto 15.
      Unshelve.
      all: exact tt.
  Qed.

  Lemma read_right_mover :
    right_mover LockAPI.step Read.
  Proof.
    unfold right_mover; intros.
    repeat step_inv; subst; eauto 15.
    destruct op1; eauto 15.
  Qed.

  Lemma write_right_mover : forall v,
      right_mover LockAPI.step (Write v).
  Proof.
    unfold right_mover; intros.
    repeat step_inv; subst; eauto 15.
    destruct op1; eauto 15.
  Qed.

  Hint Resolve acquire_right_mover.
  Hint Resolve flush_right_mover.
  Hint Resolve release_left_mover.
  Hint Resolve read_right_mover.
  Hint Resolve write_right_mover.

  Theorem ysa_movers : forall T (op : CounterOp.Op T),
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
    | H : exec_any _ _ _ (Call _) _ _ |- _ =>
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
    constructor; intros. eauto.

    repeat exec_propagate.
    unfold restricted_step in *; intuition idtac; repeat step_inv.
    constructor; intros.
  Qed.

  Hint Resolve inc_follows_protocol.
  Hint Resolve dec_follows_protocol.

  Theorem op_follows_protocol : forall tid s `(op : CounterOp.Op T),
      follows_protocol_proc RawLockAPI.step LockProtocol.step_allow tid s (compile_op op).
  Proof.
    destruct op; eauto.
  Qed.

  Theorem allowed_stable :
    forall `(op : LockOp.Op T) `(op' : LockOp.Op T') tid tid' s s' r evs,
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

(** LAYER: CounterAPI *)

Module CounterState <: State.

  Definition State := nat.
  Definition initP (s : State) := s = 0.

End CounterState.

Module CounterAPI <: Layer CounterOp CounterState.

  Import CounterOp.
  Import CounterState.

  Inductive xstep : forall T, Op T -> nat -> State -> T -> State -> list event -> Prop :=
  | StepInc : forall tid v,
      xstep Inc tid v v (v + 1) nil
  | StepDec : forall tid v,
      xstep Dec tid v v (v - 1) nil.

  Definition step := xstep.

End CounterAPI.


(** Abstracting away the lock details. *)

Module AbsCounter' <:
  LayerImplAbsT CounterOp
                LockState    LockedCounterAPI
                CounterState CounterAPI.

  Import LockState.

  Definition absR (s1 : LockState.State) (s2 : CounterState.State) :=
    Lock s1 = None /\
    empty_sb s1.(Value) /\
    s1.(Value).(MemValue) tt = s2.

  Lemma step_inc : forall tid v r v',
      r = v ->
      v' = v + 1 ->
      CounterAPI.step CounterOp.Inc tid v r v' [].
  Proof.
    intros; subst.
    constructor.
  Qed.

  Lemma step_dec : forall tid v r v',
      r = v ->
      v' = v - 1 ->
      CounterAPI.step CounterOp.Dec tid v r v' [].
  Proof.
    intros; subst.
    constructor.
  Qed.

  Hint Resolve step_inc step_dec.
  Hint Resolve empty_sb_single_value_flush.
  Hint Resolve empty_sb_mem_read.

  Lemma single_value_flush A {_:EqualDec A} T : forall (m m': memT A T) tid (f: T -> T) (a:A),
      empty_sb m ->
      single_value m' tid a (f (mem_read m a tid)) ->
      MemValue (mem_flush m' tid) a = f (MemValue m a).
  Proof.
    intros.
    assert (empty_sb (mem_flush m' tid)) by eauto.
    eapply single_value_mem_flush in H0; eauto.
    apply single_value_mem_read in H0.
    (*
    erewrite (empty_sb_mem_read (m:=(mem_flush m' tid))) in * by auto.
    erewrite (empty_sb_mem_read (m:=m)) in * by auto.
    auto.
  Qed.
     *)
  Admitted.

  Hint Resolve single_value_flush.

  Theorem absR_ok :
    op_abs absR LockedCounterAPI.step CounterAPI.step.
  Proof.
    unfold op_abs; intros.
    destruct s1; inversion H; clear H.
    simpl in *; subst; destruct_ands.
    unfold absR.
    destruct op; inv_clear H0; simpl.

    - eapply empty_sb_mem_bg_noop in H4; [ | solve [ eauto ] ]; subst.

      assert (single_value v' tid tt (mem_read Value0 tt tid + 1)).
      eapply empty_sb_single_value in H.
      eapply mem_write_single_value in H.
      eapply single_value_mem_bg in H; eauto.

      eexists; (intuition eauto).
      eapply step_inc; eauto.
      eapply single_value_flush with (f := fun x => x + 1); eauto.

    - eapply empty_sb_mem_bg_noop in H4; [ | solve [ eauto ] ]; subst.

      assert (single_value v' tid tt (mem_read Value0 tt tid - 1)).
      eapply empty_sb_single_value in H.
      eapply mem_write_single_value in H.
      eapply single_value_mem_bg in H; eauto.

      eexists; (intuition eauto).
      eapply step_dec; eauto.
      eapply single_value_flush with (f := fun x => x - 1); eauto.
  Qed.

  Theorem absInitP :
    forall s1,
      LockState.initP s1 ->
      exists s2, absR s1 s2 /\
      CounterState.initP s2.
  Proof.
    unfold absR, LockState.initP, CounterState.initP; intros.
    destruct s1; simpl in *; propositional.
    exists 0; intuition eauto.
    unfold empty_sb; simpl; auto.
  Qed.

End AbsCounter'.

Module AbsCounter :=
  LayerImplAbs CounterOp
               LockState    LockedCounterAPI
               CounterState CounterAPI
               AbsCounter'.



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

  Definition compile_op T (op : LockOp.Op T) : (option T -> TASOp.Op T) * (T -> bool) * option T :=
    match op with
    | Acquire => (fun _ => TestAndSet, acquire_cond, None)
    | Release => (fun _ => Clear, once_cond, None)
    | Read => (fun _ => TASOp.Read, once_cond, None)
    | Write v => (fun _ => TASOp.Write v, once_cond, None)
    | Flush => (fun _ => TASOp.Flush, once_cond, None)
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

  TASAPI ---------------+----+---------+
    [ AbsNondet ]       |    |         |
  TASAPI    [c0]  |         |
    [ AbsLock ]         |    |         |
  TASLockAPI -----------+   [c1]       |
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
    c0 LockImpl.
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
    (fun _ => _ <- Call Inc; _ <- Call Dec; Ret tt)
    None.

Definition test_threads : threads_state _ :=
  thread_from_list (repeat (existT _ _ test_thread) 16).

Definition compiled_threads : list (maybe_proc _) :=
  thread_to_list (c.compile_ts test_threads).
