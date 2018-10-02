Require Import CSPEC.
Require Import Helpers.Learn.
Require Import TSO.

Import ListNotations.

Global Set Implicit Arguments.
Global Generalizable All Variables.

Set Printing Projections.

Module TSOOp.

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
  | Ext : event -> xOp unit
  .

  Definition Op := xOp.

End TSOOp.

Module TSOState.

  Definition State := memT TSOOp.addr nat.

  Definition initP (s:State) :=
    s = {| MemValue := fun a => 0; SBuf := fun _ => [] |}.

End TSOState.

Definition bg_step `(step: OpSemantics Op State) (bg: State -> State -> Prop) : OpSemantics Op State :=
  fun _ op tid s r s' evs =>
    exists s0 s1, bg s0 s /\
          step _ op tid s r s1 evs /\
          bg s1 s'.

Module TSOAPI.
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
  | StepExt : forall tid ev s,
      xstep (Ext ev) tid s tt s [ev]
  .

  Definition step := bg_step xstep mem_bg.

  Definition initP := TSOState.initP.
  
  Definition l : Layer.t TSOOp.Op TSOState.State.
     refine {| Layer.step := step;
               Layer.initP := initP; |}.
  Defined.
  
End TSOAPI.

Module TSODelayNondetAPI.
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
  | StepExt : forall tid ev s,
      xstep (Ext ev) tid s tt s [ev]
  .

  Definition step := xstep.

  Definition initP := TSOState.initP.

  Definition l : Layer.t TSOOp.Op TSOState.State.
    refine {| Layer.step := step;
              Layer.initP := initP;
           |}.
  Defined.

End TSODelayNondetAPI.

(** IMPL: TSODelayNondetAPI -> TSOAPI *)

Module AbsNondet'.
  Import Layer.
  Import TSOState.

  (* absR is from low (full nondeterminism) to high (careful nondeterminism) *)
  Definition absR (s1 : State) (s2 : State) :=
    mem_bg s2 s1.

  Hint Resolve mem_bg_commute_write.
  Hint Constructors TSODelayNondetAPI.xstep.

  Theorem absR_ok :
    op_abs absR TSOAPI.l.(step) TSODelayNondetAPI.l.(step).
  Proof.
    unfold op_abs, TSODelayNondetAPI.l, TSODelayNondetAPI.step, step; intros.
    unfold absR in *.
    hnf in H0; repeat deex.
    destruct op; inv_clear H1; eauto.
    descend; split; [ | eauto ]; eauto.
    descend; split; [ | eauto ].
    etransitivity; eauto.
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

  Definition layerImplAbsT : LayerImplAbsT.t TSOAPI.l TSODelayNondetAPI.l.
    refine {| LayerImplAbsT.absR := absR;
              LayerImplAbsT.absR_ok := absR_ok;
              LayerImplAbsT.absInitP := absInitP;
           |}.
  Defined.

End AbsNondet'.

Module AbsNondet.
  Definition layerImplAbs : LayerImpl.t TSOAPI.l TSODelayNondetAPI.l.
    refine (LayerImplAbs.t AbsNondet'.layerImplAbsT).
  Defined.
End AbsNondet.

(** LAYER: TASAPI *)

Module TASOp.

  Inductive xOp : Type -> Type :=
  | TryAcquire : xOp bool (* true if acquired *)
  | Clear : xOp unit
  | Read : xOp nat
  | Write : nat -> xOp unit
  | Ext : event -> xOp unit
  .

  Definition Op := xOp.

End TASOp.

Module TAS_TSOAPI.
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
  | StepExt : forall tid ev s,
      xstep (Ext ev) tid s tt s [ev]
  .

  Definition step := xstep.

  Definition initP := TSOState.initP.

  Definition l : Layer.t Op State.
    refine {| Layer.step := step;
              Layer.initP := initP; |}.
  Defined.
    
End TAS_TSOAPI.

Module TAS_TSOImpl'. 
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
    | TASOp.Ext ev => Call (Ext ev)
    end.

  Theorem compile_op_no_atomics : forall T (op: TASOp.Op T),
      no_atomics (compile_op op).
  Proof.
    destruct op; simpl; eauto using no_atomics.
  Qed.

  Hint Constructors xstep.

  Theorem ysa_movers :
    forall (T : Type) (op : TASOp.Op T),
      ysa_movers l.(Layer.step) (compile_op op).
  Proof.
    destruct op; simpl; eauto.
  Qed.

  Hint Constructors TAS_TSOAPI.xstep.

  Theorem compile_correct :
    compile_correct compile_op l.(Layer.step) TAS_TSOAPI.l.(Layer.step).
  Proof.
    unfold TAS_TSOAPI.l, Layer.step, TAS_TSOAPI.step.
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

  Definition initP_compat : forall s,
      l.(Layer.initP) s -> TAS_TSOAPI.l.(Layer.initP) s := ltac:(auto).

  Definition layerImplMoversT : LayerImplMoversT.t TSODelayNondetAPI.l TAS_TSOAPI.l.
    refine {| LayerImplMoversT.compile_op := compile_op;
              LayerImplMoversT.compile_op_no_atomics := compile_op_no_atomics;
              LayerImplMoversT.ysa_movers := ysa_movers;
              LayerImplMoversT.compile_correct := compile_correct;
              LayerImplMoversT.initP_compat := initP_compat; |}.
  Defined.

End TAS_TSOImpl'.

Module TAS_TSOImpl.
  Definition t : LayerImpl.t TSODelayNondetAPI.l TAS_TSOAPI.l.
    refine (LayerImplMovers.t TAS_TSOImpl'.layerImplMoversT).
  Defined.
End TAS_TSOImpl.

Inductive OrError State :=
| Valid (s:State)
| Error.
Arguments Error {State}.

Inductive error_step Op State
          {step: OpSemantics Op State}
          {violation: forall T, Op T -> nat -> State -> Prop} :
  OpSemantics Op (OrError State) :=
| valid_step : forall T (op: Op T) tid s r s' evs,
    step _ op tid s r s' evs ->
    error_step op tid (Valid s) r (Valid s') evs
| invalid_step : forall T (op: Op T) tid s r evs,
    violation _ op tid s ->
    error_step op tid (Valid s) r Error evs
| invalid_preserved : forall T (op: Op T) tid s r r' s' evs,
    step _ op tid s r s' evs ->
    (* any return value - makes things a bit more convenient since we don't need
    restricted return values *)
    error_step op tid Error r' Error evs
.

Arguments error_step {Op State} step violation.

Module LockOwnerState.

  Record s := mkLOState {
                  TASValue : memT TSOOp.addr nat;
                  TASLock : option nat;
                }.
  Definition State := OrError s.

  Definition initP s :=
    s = Valid {| TASValue := {| MemValue := fun _ => 0; SBuf := fun _ => [] |};
                 TASLock := None |}.
End LockOwnerState.


Definition bad_lock T (op: TASOp.Op T) tid (l: option nat) :=
  match op with
  | TASOp.TryAcquire => False
  | TASOp.Ext _ => False
  | _ => l <> Some tid
  end.

Definition decide_violation T (op: TASOp.Op T) tid l :
  {bad_lock op tid l} + {match op with
                         | TASOp.TryAcquire => True
                         | TASOp.Ext _ => True
                          | _ => l = Some tid
                          end}.
Proof.
  destruct op, (l == Some tid); subst; eauto.
Qed.

Module LockOwnerAPI.

  Import TSOOp.
  Import TASOp.
  Import LockOwnerState.

  Inductive xstep : OpSemantics Op s :=
  | StepTryAcquireSuccess : forall tid s l s',
      mem_bg s s' ->
      mem_read s' Lock tid <> cLocked ->
      xstep TryAcquire tid
            (mkLOState s l)
            true
            (mkLOState (mem_flush (mem_write Lock cLocked s' tid) tid) (Some tid))
            nil
  | StepTryAcquireFail : forall tid s s' l,
      mem_bg s s' ->
      xstep TryAcquire tid
            (mkLOState s l)
            false
            (mkLOState (mem_flush s' tid) l)
            nil
  | StepClear : forall tid s,
      xstep Clear tid (mkLOState s (Some tid))
            tt
            (mkLOState (mem_write Lock cUnlocked s tid) None)
            nil
  | StepRead : forall tid s s',
      mem_bg s s' ->
      xstep Read tid
            (mkLOState s (Some tid))
            (mem_read s' Val tid)
            (mkLOState s' (Some tid))
            nil
  | StepWrite : forall tid s v,
      xstep (Write v) tid
            (mkLOState s (Some tid))
            tt
            (mkLOState (mem_write Val v s tid) (Some tid))
            nil
  | StepExt : forall tid ev s,
      xstep (Ext ev) tid s tt s [ev]
  .

  Definition step := error_step xstep (fun T op tid s => bad_lock op tid s.(TASLock)).

  Definition initP := LockOwnerState.initP.

  Definition l : Layer.t Op LockOwnerState.State.
    refine {| Layer.step := step;
              Layer.initP := initP; |}.
  Defined.

End LockOwnerAPI.


Module AbsLockOwner'.
  Import TSOOp.
  Import TASOp.
  Import TSOState LockOwnerState.

  Definition absR (s1: TSOState.State) (s2: State) :=
    forall s2', s2 = Valid s2' ->
           s2'.(TASValue) = s1.

  Theorem absR_error : forall s1,
      absR s1 Error.
  Proof.
    unfold absR; congruence.
  Qed.

  Theorem absR_intro : forall s1 l,
      absR s1 (Valid (mkLOState s1 l)).
  Proof.
    unfold absR; intros.
    invert H; simpl; auto.
  Qed.

  Import LockOwnerAPI.

  Hint Resolve absR_error absR_intro.
  Hint Constructors error_step.
  Hint Constructors xstep.
  Hint Resolve None.

  Theorem absR_ok : op_abs absR TAS_TSOAPI.l.(Layer.step) l.(Layer.step).
  Proof.
    unfold l, Layer.step, step.
    hnf; intros.
    destruct s2; unfold absR in * |- ; simpl in *; propositional.
    - specialize (H _ eq_refl); subst.
      destruct (decide_violation op tid s0.(TASLock)).
      + exists Error; intuition eauto.
      + destruct s0; simpl in *.
        invert H0; subst;
          try solve [ eexists (Valid _); split; eauto ].
    - eexists; split; [ apply absR_error | ].
      invert H0; eauto.
      Grab Existential Variables.
      all: auto.
      constructor; eauto.
  Qed.

  Theorem absInitP :
    forall s1,
      TAS_TSOAPI.l.(Layer.initP) s1 ->
      exists s2 : State, absR s1 s2 /\ l.(Layer.initP) s2.
  Proof.
    unfold TAS_TSOAPI.l, l, Layer.initP, TAS_TSOAPI.initP, TSOState.initP, initP, LockOwnerState.initP; propositional.
    exists_econstructor; eauto.
  Qed.

  Definition layerImplAbsT : LayerImplAbsT.t TAS_TSOAPI.l LockOwnerAPI.l.
    refine {| LayerImplAbsT.absR := absR;
              LayerImplAbsT.absR_ok := absR_ok;
              LayerImplAbsT.absInitP := absInitP;
           |}.
  Defined.
End AbsLockOwner'.

Module AbsLockOwner.
  Definition t : LayerImpl.t TAS_TSOAPI.l LockOwnerAPI.l.
    refine (LayerImplAbs.t AbsLockOwner'.layerImplAbsT).
  Defined.
End AbsLockOwner.

Module LockInvariantState.

  Record s := mkLIState {
                  InvValue : memT TSOOp.addr nat;
                  InvLock : option nat;
                  PrevOwner : nat;
                }.

  Definition State := OrError s.

  Definition initP s :=
    s = Valid {| InvValue :=
                   {| MemValue := fun a => 0; SBuf := fun _ => [] |};
                 InvLock := None;
                 PrevOwner := 0 |}.

End LockInvariantState.


Definition empty_sb_except A T (m: memT A T) tid :=
  forall tid', tid <> tid' ->
          m.(SBuf) tid' = [].

Lemma empty_sb_to_empty_sb_except : forall A V (m: memT A V) (a:nat),
    empty_sb m ->
    empty_sb_except m a.
Proof.
  firstorder.
Qed.

Hint Resolve empty_sb_to_empty_sb_except.

Definition only_val (sbuf: list (TSOOp.addr * nat)) :=
  List.Forall (fun '(a, _) => a = TSOOp.Val) sbuf.

Lemma only_val_empty : only_val [].
Proof.
  unfold only_val; eauto.
Qed.

Hint Resolve only_val_empty.

Definition unlock_last (sbuf: list (TSOOp.addr * nat)) :=
  exists l, sbuf = (TSOOp.Lock, TSOOp.cUnlocked) :: l /\
       only_val l.

Module LockInvariantAPI.

  Import TSOOp.
  Import TASOp.
  Import LockInvariantState.

  Definition invariant (s:LockInvariantState.s) :=
    match s.(InvLock) with
    | Some tid => empty_sb_except s.(InvValue) tid /\
                 s.(PrevOwner) = tid /\
                 only_val (s.(InvValue).(SBuf) tid) /\
                 s.(InvValue).(MemValue) Lock = cLocked
    | None => (s.(InvValue).(MemValue) Lock <> cLocked /\
              empty_sb s.(InvValue)) \/
             (s.(InvValue).(MemValue) Lock = cLocked /\
              empty_sb_except s.(InvValue) s.(PrevOwner) /\
              unlock_last (s.(InvValue).(SBuf) s.(PrevOwner)))
    end.

  Lemma invariant_owned_pl : forall s tid pl,
      invariant (mkLIState s (Some tid) pl) ->
      pl = tid.
  Proof.
    unfold invariant; simpl; propositional.
  Qed.

  Lemma invariant_empty_sb : forall s l pl,
      invariant (mkLIState s l pl) ->
      empty_sb_except s pl.
  Proof.
    unfold invariant; simpl; intros.
    destruct l; propositional.
    intuition eauto.
  Qed.

  Inductive xstep : OpSemantics Op s :=
  | StepTryAcquireSuccess : forall tid s s' pl,
      mem_bg s s' ->
      mem_read s' Lock tid <> cLocked ->
      xstep TryAcquire tid
            (mkLIState s None pl)
            true
            (mkLIState (mem_flush (mem_write Lock cLocked s' tid) tid) (Some tid) tid) nil
  | StepTryAcquireFail : forall tid s s' l pl,
      mem_bg s s' ->
      xstep TryAcquire tid
            (mkLIState s l pl)
            false
            (mkLIState (mem_flush s' tid) l pl) nil
  | StepClear : forall tid v pl,
      xstep Clear tid
            (mkLIState v (Some tid) pl)
            tt
            (mkLIState (mem_write Lock cUnlocked v tid) None pl) nil
  | StepRead : forall tid s s' pl,
      mem_bg s s' ->
      xstep Read tid
            (mkLIState s (Some tid) pl)
            (mem_read s' Val tid)
            (mkLIState s' (Some tid) pl) nil
  | StepWrite : forall tid s v' pl,
      xstep (Write v') tid
            (mkLIState s (Some tid) pl)
            tt
            (mkLIState (mem_write Val v' s tid) (Some tid) pl) nil
  | StepExt : forall tid ev s,
      xstep (Ext ev) tid s tt s [ev]
  .

  Definition invariant_step (s1 s2:s) :=
    invariant s1 /\ s2 = s1.

  Definition step := error_step
                       (bg_step xstep invariant_step)
                       (fun T op tid s => bad_lock op tid s.(InvLock)).

  Definition initP := initP.

  Definition l : Layer.t Op State.
     refine {| Layer.step := step;
               Layer.initP := initP; |}.
  Defined.
End LockInvariantAPI.

Inductive error_absR {State1 State2} {absR: State1 -> State2 -> Prop} :
  OrError State1 -> OrError State2 -> Prop :=
| absR_error : error_absR Error Error
| absR_valid : forall s1 s2,
    absR s1 s2 ->
    error_absR (Valid s1) (Valid s2).

Arguments error_absR {State1 State2} absR.

Hint Constructors error_absR.

Module AbsLockInvariant'.
  Import TSOOp.
  Import TASOp.
  Import LockOwnerState LockInvariantState.

  Import LockInvariantAPI.

  Definition abstr (s1: LockOwnerState.s) (s2: s) :=
    s2.(InvValue) = s1.(TASValue) /\
    s2.(InvLock) = s1.(TASLock) /\
    invariant s2.

  Lemma abstr_invlock : forall s1 s2,
      abstr s1 s2 ->
      s2.(InvLock) = s1.(TASLock).
  Proof.
    firstorder.
  Qed.

  Definition absR := error_absR abstr.

  Lemma abstr_intro : forall v l pl,
      invariant (mkLIState v l pl) ->
      error_absR abstr (Valid (mkLOState v l)) (Valid (mkLIState v l pl)).
  Proof.
    intros.
    constructor.
    unfold abstr; intuition eauto.
  Qed.

  Lemma abstr_invariant : forall s1 s2,
      abstr s1 s2 ->
      invariant s2.
  Proof.
    firstorder.
  Qed.

  Hint Resolve abstr_invariant.

  Lemma bg_invariant : forall T (op: Op T) tid s v s' evs,
      xstep op tid s v s' evs ->
      invariant s ->
      invariant s' ->
      bg_step xstep invariant_step op tid s v s' evs.
  Proof.
    intros.
    unfold bg_step.
    unfold invariant_step.
    descend; (intuition idtac);
      try reflexivity;
      eauto.
  Qed.

  Hint Constructors xstep.

  Lemma mem_bgflush_other_tid : forall A {Adec:EqualDec A} V (m: memT A V) tid tid',
      tid <> tid' ->
      (mem_bgflush m tid').(SBuf) tid = m.(SBuf) tid.
  Proof.
    unfold mem_bgflush; intros.
    destruct matches; subst; simpl.
    autorewrite with fupd; auto.
  Qed.

  Theorem mem_bg_empty_sb_except : forall A {Aeq:EqualDec A} V (s s': memT A V) tid,
      empty_sb_except s tid ->
      mem_bg s s' ->
      empty_sb_except s' tid.
  Proof.
    unfold empty_sb_except; intros.
    specialize (H _ ltac:(eauto)).
    induction H0; propositional.
    destruct (tid' == tid0); subst.
    rewrite mem_bgflush_noop by auto; auto.
    rewrite mem_bgflush_other_tid by auto; auto.
  Qed.

  Hint Resolve mem_bg_empty_sb_except.

  Theorem last_error_app : forall A (l l': list A) a,
      last_error (l ++ a::l') = last_error (a::l').
  Proof.
    induction l0; simpl; intros; eauto.
    rewrite IHl0.
    simpl.
    destruct_with_eqn (l0 ++ a0 :: l'); auto.
    apply app_eq_nil in Heql1; intuition congruence.
  Qed.

  Theorem last_error_app1 : forall A (l: list A) x,
      last_error (l ++ [x]) = Some x.
  Proof.
    intros.
    rewrite last_error_app.
    auto.
  Qed.

  Lemma unlocked_not_locked : cUnlocked = cLocked -> False.
  Proof.
    unfold cUnlocked, cLocked; omega.
  Qed.

  Hint Resolve unlocked_not_locked.

  Lemma empty_sb_except_to_all : forall A {Aeq:EqualDec A} V (m: memT A V) a,
      empty_sb_except m a ->
      m.(SBuf) a = [] ->
      empty_sb m.
  Proof.
    unfold empty_sb, empty_sb_except; intros.
    destruct (a == tid); subst; eauto.
  Qed.

  Lemma empty_sb_except_mem_bgflush : forall A {Aeq:EqualDec A} V (m: memT A V) tid tid',
      empty_sb_except m tid ->
      empty_sb_except (mem_bgflush m tid') tid.
  Proof.
    unfold empty_sb_except; intros.
    destruct (tid == tid'); subst.
    - unfold mem_bgflush.
      destruct matches; subst; simpl;
        autorewrite with fupd;
        auto.
    - rewrite mem_bgflush_empty_sbuf by auto; eauto.
  Qed.

  Lemma empty_sb_except_mem_flush : forall A {Aeq:EqualDec A} V (m: memT A V) tid tid',
      empty_sb_except m tid ->
      empty_sb_except (mem_flush m tid') tid.
  Proof.
    unfold empty_sb_except; intros.
    unfold mem_flush; simpl.
    destruct (tid' == tid'0); subst; autorewrite with fupd; auto.
  Qed.

  Lemma empty_sb_except_write : forall A {Aeq:EqualDec A} V (m: memT A V) tid a v,
      empty_sb_except m tid ->
      empty_sb_except (mem_write a v m tid) tid.
  Proof.
    unfold empty_sb_except; intros.
    unfold mem_write; simpl; autorewrite with fupd; eauto.
  Qed.

  Lemma empty_sb_except_mem_flush_write : forall A {Aeq:EqualDec A} V (m: memT A V) tid a v tid',
      empty_sb_except m tid ->
      empty_sb_except (mem_flush (mem_write a v m tid') tid') tid.
  Proof.
    unfold empty_sb_except; simpl; intros.
    destruct (tid' == tid'0); subst; autorewrite with fupd; eauto.
  Qed.

  Hint Resolve
       empty_sb_except_mem_bgflush
       empty_sb_except_mem_flush
       empty_sb_except_write
       empty_sb_except_mem_flush_write.

  Lemma Forall_app : forall A (P: A -> Prop) (l1 l2: list A),
      Forall P (l1 ++ l2) ->
      Forall P l1 /\ Forall P l2.
  Proof.
    induction l1; simpl; intros; auto.
    invert H.
    epose_proof IHl1; eauto; propositional.
    eauto.
  Qed.

  Lemma Forall_removelast : forall A (l: list A) (P: A -> Prop),
      Forall P l ->
      Forall P (removelast l).
  Proof.
    induction l0 using rev_ind; intros; eauto.
    apply Forall_app in H; propositional.
    rewrite removelast_app_one; auto.
  Qed.

  Lemma only_val_removelast : forall l,
      only_val l ->
      only_val (removelast l).
  Proof.
    unfold only_val; eauto using Forall_removelast.
  Qed.

  Hint Resolve only_val_removelast.

  Lemma only_val_mem_bgflush:
    forall (m : memT addr nat) (tid tid' : nat),
      only_val (m.(SBuf) tid) ->
      only_val ((mem_bgflush m tid').(SBuf) tid).
  Proof.
    intros.
    unfold mem_bgflush; simpl.
    destruct (tid == tid');
      destruct matches; subst; simpl; autorewrite with fupd; eauto.
  Qed.

  Hint Resolve only_val_mem_bgflush.
  Hint Rewrite mem_flush_empty_sbuf using solve [ auto ] : tso.
  Hint Rewrite mem_bgflush_empty_sbuf using solve [ auto ] : tso.

  Lemma mem_bgflush_last : forall A {Aeq:EqualDec A} V (m: memT A V) tid (a:A) l v,
      m.(SBuf) tid = l ++ [(a,v)] ->
      (mem_bgflush m tid).(MemValue) a = v.
  Proof.
    unfold mem_bgflush; simpl; intros.
    rewrite H.
    rewrite last_error_append; simpl; autorewrite with fupd; auto.
  Qed.

  Lemma empty_sb_bgflush_last : forall A {Aeq:EqualDec A} V (m:memT A V) tid w,
      m.(SBuf) tid = [w] ->
      empty_sb_except m tid ->
      empty_sb (mem_bgflush m tid).
  Proof.
    destruct w; intros.
    eapply empty_sb_except_to_all; eauto.
    unfold mem_bgflush.
    rewrite H; simpl; autorewrite with fupd; auto.
  Qed.

  Hint Resolve empty_sb_bgflush_last.

  Theorem val_not_lock : Val <> Lock.
  Proof.
    compute; congruence.
  Qed.

  Hint Resolve val_not_lock.

  Lemma flush_only_val_lock : forall m tid,
      only_val (m.(SBuf) tid) ->
      (mem_bgflush m tid).(MemValue) Lock = m.(MemValue) Lock.
  Proof.
    unfold only_val, mem_bgflush; intros.
    generalize dependent (m.(SBuf) tid); intros.
    destruct (list_last_dec l0); propositional; simpl; auto.
    destruct a.
    apply Forall_app in H; propositional.
    invert H0; clear H0.
    rewrite last_error_append; simpl; autorewrite with fupd; auto.
  Qed.

  Hint Rewrite flush_only_val_lock using solve [ auto ] : tso.

  Lemma flush_val_lock : forall V (m: memT addr V) tid l v,
      m.(SBuf) tid = l ++ [(Val, v)] ->
      (mem_bgflush m tid).(MemValue) Lock = m.(MemValue) Lock.
  Proof.
    unfold mem_bgflush; intros.
    rewrite H.
    rewrite last_error_append; simpl; autorewrite with fupd; auto.
  Qed.

  Lemma last_error_cons : forall A (a:A) l,
      last_error (a :: l) <> None.
  Proof.
    induction l0; simpl in *; try congruence.
    destruct l0; try congruence.
  Qed.

  Lemma last_error_cons2 : forall A (l: list A) x y,
      last_error (x :: y :: l) = last_error (y :: l).
  Proof.
    simpl; auto.
  Qed.

  Lemma last_error_Forall : forall A a (l: list A) P,
      Forall P (a :: l) ->
      exists y, last_error (a :: l) = Some y /\
           P y.
  Proof.
    intros.
    simpl.
    induction l0 using rev_ind.
    - invert H; eauto.
    - rewrite app_comm_cons in H.
      apply Forall_app in H; propositional.
      invert H0; clear H0.
      rewrite last_error_append.
      destruct l0; simpl; eauto.
  Qed.

  Definition unlock_last_bgflush : forall m tid,
      unlock_last (m.(SBuf) tid) ->
      { (mem_bgflush m tid).(MemValue) Lock = cUnlocked /\
        (mem_bgflush m tid).(SBuf) tid = []} +
      {(mem_bgflush m tid).(MemValue) Lock = m.(MemValue) Lock /\
       unlock_last ((mem_bgflush m tid).(SBuf) tid) }.
  Proof.
    unfold mem_bgflush; simpl; propositional.
    generalize dependent (m.(SBuf) tid); intros.
    destruct l0.
    - exfalso.
      unfold unlock_last in H; propositional; congruence.
    - destruct l0;
        [ left | right ];
        unfold unlock_last in *; propositional.
      + invert H; clear H; simpl; autorewrite with fupd; auto.
      + destruct p0.
        invert H; clear H; autorewrite with fupd; auto.
        invert H0.
        split.
        * rewrite last_error_cons2.
          pose proof (last_error_Forall H0); propositional.
          rewrite H.
          destruct y; subst; simpl; autorewrite with fupd; auto.
        * exists (removelast ((Val,n) :: l0)); (intuition auto).
          destruct matches; simpl; autorewrite with fupd; auto.
          apply last_error_cons in Heqo; propositional.
  Qed.

  Hint Resolve addr_equal_dec.

  Theorem invariant_mem_bgflush : forall s s' l pl tid,
      invariant (mkLIState s l pl) ->
      s' = mem_bgflush s tid ->
      invariant (mkLIState s' l pl).
  Proof.
    unfold invariant; simpl; propositional; intuition eauto.
    destruct l0; (intuition eauto); propositional;
      autorewrite with tso;
      eauto.
    destruct (n == tid); subst; autorewrite with tso; auto.

    destruct (tid == pl); subst.
    - destruct (unlock_last_bgflush s0 pl ltac:(eassumption)); propositional;
        [ left | right ].
      + intuition eauto.
        cut (cUnlocked = cLocked); try congruence; eauto.
        eapply empty_sb_except_to_all; eauto.
      + intuition eauto.
        congruence.
    - autorewrite with tso; eauto.
  Qed.

  Theorem invariant_mem_bg : forall s s' l pl,
      invariant (mkLIState s l pl) ->
      mem_bg s s' ->
      invariant (mkLIState s' l pl).
  Proof.
    intros.
    eapply mem_bgflush_mem_bg_invariant with
        (I:=fun s => invariant (mkLIState s l0 pl)); eauto.
    intros.
    eapply invariant_mem_bgflush; eauto.
  Qed.

  Theorem invariant_mem_flush : forall s s' l pl tid,
      invariant (mkLIState s l pl) ->
      s' = mem_flush s tid ->
      invariant (mkLIState s' l pl).
  Proof.
    intros; subst.
    eapply mem_bgflush_mem_flush_invariant with
        (I:=fun s => invariant (mkLIState s l0 pl)); eauto.
    intros.
    eapply invariant_mem_bgflush; eauto.
  Qed.

  Hint Resolve addr_equal_dec.

  Lemma mem_read_empty_sbuf : forall A {Aeq:EqualDec A} V (m: memT A V) a tid,
      m.(SBuf) tid = [] ->
      mem_read m a tid = m.(MemValue) a.
  Proof.
    unfold mem_read; intros.
    rewrite H; simpl; auto.
  Qed.

  Hint Rewrite mem_read_empty_sbuf using solve [ auto ] : tso.

  Lemma mem_read_only_val:
    forall (m : memT addr nat) (tid' tid : nat),
      empty_sb_except m tid ->
      only_val (m.(SBuf) tid) ->
      mem_read m Lock tid' = m.(MemValue) Lock.
  Proof.
    unfold empty_sb_except; intros.
    destruct (tid == tid'); subst; autorewrite with tso; auto.
    clear H.
    unfold mem_read; simpl.
    unfold only_val in *.
    generalize dependent (m.(SBuf) tid'); intros.
    induction l0; simpl; auto.
    invert H0; clear H0.
    destruct a; subst.
    destruct (Lock == Val); subst; eauto.
    exfalso; eauto.
  Qed.

  Theorem invariant_write_lock : forall s tid l pl,
      invariant (mkLIState s l pl) ->
      mem_read s Lock tid <> cLocked ->
      invariant (mkLIState
                   (mem_flush (mem_write Lock cLocked s tid) tid)
                   (Some tid)
                   tid).
  Proof.
    unfold invariant; simpl; propositional.
    destruct l0; propositional; autorewrite with fupd; intuition eauto.
    - erewrite mem_read_only_val in H0 by eauto; contradiction.
    - destruct (tid == pl); subst; eauto.
      autorewrite with tso in *; contradiction.
  Qed.

  Lemma invariant_write_unlock : forall s tid pl,
      invariant (mkLIState s (Some tid) pl) ->
      invariant (mkLIState (mem_write Lock cUnlocked s tid) None pl).
  Proof.
    unfold invariant; simpl; propositional; autorewrite with fupd.
    right; intuition eauto.
    unfold unlock_last.
    eexists; eauto.
  Qed.

  Lemma invariant_write_val : forall s v tid pl,
      invariant (mkLIState s (Some tid) pl) ->
      invariant (mkLIState (mem_write Val v s tid) (Some tid) pl).
  Proof.
    unfold invariant; simpl; propositional; autorewrite with fupd.
    intuition eauto.
    constructor; eauto.
  Qed.

  Lemma no_step_on_violation:
    forall (T : Type) (op : Op T) (tid : nat) (r : T) (evs : list event)
      (s0 s' : LockOwnerState.s),
      LockOwnerAPI.xstep op tid s0 r s' evs ->
      bad_lock op tid s0.(TASLock) ->
      False.
  Proof.
    unfold bad_lock.
    intros.
    invert H; eauto.
  Qed.

  Theorem abstr_lock_same : forall s s',
      abstr s s' ->
      s'.(InvLock) = s.(TASLock).
  Proof.
    firstorder.
  Qed.

  Section ErrorStep.

    Definition trivial_mem l : memT addr nat := {| MemValue := fun a => if a == Lock then l else 0; SBuf := fun _ => [] |}.

    Lemma trivial_read_lock : forall tid l,
        mem_read (trivial_mem l) Lock tid = l.
    Proof.
      reflexivity.
    Qed.

    Lemma trivial_empty_sb l : empty_sb (trivial_mem l).
    Proof.
      repeat (hnf; intros); eauto.
    Qed.

    Hint Resolve trivial_empty_sb.

    Hint Resolve only_val_empty.

    Lemma try_acquire_step : forall tid,
        exists s r s',
          bg_step xstep invariant_step TryAcquire tid s r s' [].
    Proof.
      intros.
      eexists
        (mkLIState (trivial_mem cUnlocked) None tid),
      true,
      (mkLIState _ (Some tid) tid).
      eapply bg_invariant; eauto.
      eapply StepTryAcquireSuccess.
      reflexivity.
      rewrite trivial_read_lock; eauto.
      unfold invariant; simpl; eauto.
      unfold invariant; simpl; eauto.
      autorewrite with fupd; intuition eauto.
    Qed.

    Hint Resolve try_acquire_step.

    Hint Resolve empty_sb_to_empty_sb_except.

    Lemma step_any_op : forall T (op: Op T) tid s0 r0 s1 evs,
        LockOwnerAPI.xstep op tid s0 r0 s1 evs ->
        exists s r s',
          bg_step xstep invariant_step op tid s r s' evs.
    Proof.
      intros.
      invert H; eauto.
      - eexists
          (mkLIState (trivial_mem cLocked) (Some tid) tid),
        tt,
        (mkLIState _ None tid).
        eapply bg_invariant; eauto.
        + unfold invariant; simpl; eauto.
        + unfold invariant; simpl; eauto.
          right; intuition eauto.
          unfold empty_sb_except, trivial_mem; simpl; intros.
          autorewrite with fupd; auto.
          unfold unlock_last; autorewrite with fupd; eauto.
      - eexists
          (mkLIState (trivial_mem cLocked) (Some tid) tid),
        _,
          (mkLIState (trivial_mem cLocked) (Some tid) tid).
        eapply bg_invariant; eauto.
        + constructor.
          reflexivity.
        + unfold invariant; simpl; eauto.
        + unfold invariant; simpl; eauto.
      - eexists
          (mkLIState (trivial_mem cLocked) (Some tid) tid),
        _,
          (mkLIState _ (Some tid) tid).
        eapply bg_invariant; eauto.
        + unfold invariant; simpl; eauto.
        + unfold invariant; simpl; intuition eauto.
          unfold empty_sb_except, trivial_mem; simpl; intros.
          autorewrite with fupd; auto.
          unfold unlock_last; autorewrite with fupd; eauto.
          unfold only_val; auto.
      - eexists
          (mkLIState (trivial_mem cUnlocked) None 0),
        tt,
        _.
        eapply bg_invariant; eauto.
        + unfold invariant; simpl; eauto.
        + unfold invariant; simpl; eauto.
    Qed.
  End ErrorStep.

  Lemma observe_unlock_mem_read :
    forall tid pl (s : memT addr nat) (l : option nat),
      invariant {| InvValue := s; InvLock := l; PrevOwner := pl |} ->
      forall s' : memT addr nat,
        mem_bg s s' ->
        mem_read s' Lock tid <> cLocked ->
        l = None.
  Proof.
    intros.
    eapply invariant_mem_bg in H; eauto.
    unfold invariant in *; simpl in *; propositional.
    destruct l0; propositional; auto.
    exfalso.
    destruct (n == tid); subst; autorewrite with tso in *; eauto.
    erewrite mem_read_only_val in H1 by eauto; congruence.
  Qed.

  Ltac fwd :=
    repeat match goal with
           | [ H: invariant (mkLIState ?s ?l ?pl),
                  H': mem_bg ?s _ |- _ ] =>
             learn that (invariant_mem_bg l pl H H')
           end.

  Theorem absR_ok : op_abs absR LockOwnerAPI.l.(Layer.step) l.(Layer.step).
  Proof.
    unfold LockOwnerAPI.l, l, Layer.step, LockOwnerAPI.step, step, absR.
    hnf; intros.
    invert H0; clear H0.
    - invert H; clear H; eauto.
      destruct (decide_violation op tid s0.(TASLock)).
      + exfalso.
        eauto using no_step_on_violation.
      + unfold abstr in * |- .
        destruct s3; simpl in *; propositional.
        invert H6; simpl in *.
        * eexists; split; [ eapply abstr_intro with (pl:=tid) | ]; fwd.
          eapply invariant_mem_bg in H1; eauto.
          eapply invariant_write_lock; eauto.
          constructor.
          apply bg_invariant; eauto.
          assert (l0 = None); subst.
          eauto using observe_unlock_mem_read.
          constructor; eauto.
          eapply invariant_write_lock; eauto.
        * eexists; split; [ eapply abstr_intro with (pl:=PrevOwner0) | ]; fwd.
          eapply invariant_mem_flush; eauto.
          constructor.
          apply bg_invariant; eauto.
          eapply invariant_mem_flush; eauto.
        * eexists; split; [ eapply abstr_intro with (pl := PrevOwner0) | ]; fwd.
          eapply invariant_write_unlock; eauto.
          constructor.
          apply bg_invariant; eauto.
          eapply invariant_write_unlock; eauto.
        * eexists; split; [ eapply abstr_intro with (pl := PrevOwner0) | ]; fwd.
          eauto.
          constructor.
          apply bg_invariant; eauto.
        * eexists; split; [ eapply abstr_intro with (pl := PrevOwner0) | ]; fwd.
          eapply invariant_write_val; eauto.
          constructor.
          apply bg_invariant; eauto.
          eapply invariant_write_val; eauto.
        * destruct s'.
          eexists; split; [ eapply abstr_intro with (pl := PrevOwner0) | ]; eauto; fwd.
          constructor.
          apply bg_invariant; eauto.
    - invert H.
      exists Error; intuition eauto.
      econstructor.
      erewrite abstr_lock_same by eauto; eauto.
    - invert H; clear H.
      exists Error; split; eauto.
      apply step_any_op in H6; propositional; eauto.
  Qed.

  Theorem absInitP :
    forall s1,
      LockOwnerState.initP s1 ->
      exists s2 : State, absR s1 s2 /\ initP s2.
  Proof.
    unfold LockOwnerState.initP, initP, LockInvariantState.initP; propositional.
    exists_econstructor; intuition eauto.
    constructor.
    unfold abstr; intuition eauto.
    hnf; simpl; eauto.
    left.
    intuition eauto.
    unfold empty_sb; intros; eauto.
  Qed.

  Definition layerImplAbsT : LayerImplAbsT.t LockOwnerAPI.l LockInvariantAPI.l.
    refine {| LayerImplAbsT.absR := absR;
              LayerImplAbsT.absR_ok := absR_ok;
              LayerImplAbsT.absInitP := absInitP;
           |}.
  Defined.
End AbsLockInvariant'.

Module AbsLockInvariant.
  Definition t : LayerImpl.t LockOwnerAPI.l LockInvariantAPI.l.
    refine (LayerImplAbs.t AbsLockInvariant'.layerImplAbsT).
  Defined.
End AbsLockInvariant.

Module SeqMemState.

  Record s := mkSMState {
                  Value : nat;
                  LockOwner : option nat;
                }.

  Definition State := OrError s.

  Definition initP s :=
    s = Valid {| Value := 0; LockOwner := None |}.
End SeqMemState.


Module SeqMemAPI.

  Import TASOp.
  Import SeqMemState.

  Inductive xstep : OpSemantics Op s :=
  | StepTryAcquireSuccess : forall tid v,
      xstep TryAcquire tid (mkSMState v None) true (mkSMState v (Some tid)) nil
  | StepTryAcquireFail : forall tid v l,
      xstep TryAcquire tid (mkSMState v l) false (mkSMState v l) nil
  | StepClear : forall tid v,
      xstep Clear tid (mkSMState v (Some tid)) tt (mkSMState v None) nil
  | StepRead : forall tid v,
      xstep Read tid (mkSMState v (Some tid)) v (mkSMState v (Some tid)) nil
  | StepWrite : forall tid v v',
      xstep (Write v') tid (mkSMState v (Some tid)) tt (mkSMState v' (Some tid)) nil
  | StepExt : forall tid ev s,
      xstep (Ext ev) tid s tt s [ev]
  .

  Definition step := error_step xstep (fun T op tid s => bad_lock op tid s.(LockOwner)).

  Definition initP := initP.
  Definition l : Layer.t Op State.
     refine {| Layer.step := step;
               Layer.initP := initP; |}.
  Defined.
End SeqMemAPI.


Module AbsSeqMem'.

  Import TSOOp.
  Import TASOp.
  Import LockInvariantState SeqMemState.

  Definition abstr (s1: LockInvariantState.s) (s2: SeqMemState.s) : Prop :=
    s1.(InvLock) = s2.(LockOwner) /\
    mem_read s1.(InvValue) Val s1.(PrevOwner) = s2.(Value).

  Lemma abstr_lockowner : forall s1 s2,
      abstr s1 s2 ->
      s1.(InvLock) = s2.(LockOwner).
  Proof.
    firstorder.
  Qed.

  Hint Resolve (ltac:(inversion 1) : Val <> Lock).

  Hint Rewrite mem_read_mem_flush_eq : tso.
  Hint Rewrite mem_read_mem_bgflush_eq : tso.
  Hint Rewrite mem_read_mem_write_ne using solve [ auto ] : tso.
  Hint Rewrite mem_read_mem_write_eq : tso.
  Hint Rewrite mem_flush_empty_sbuf using solve [ auto ] : tso.
  Hint Rewrite mem_bgflush_empty_sbuf using solve [ auto ] : tso.

  Import LockInvariantAPI.
  Import SeqMemAPI.

  Theorem mem_bg_preserves_abstr' : forall s s' l pl l' v,
      invariant (mkLIState s l pl) /\
      abstr (mkLIState s l pl) (mkSMState v l') ->
      mem_bg s s' ->
      invariant (mkLIState s' l pl) /\
      abstr (mkLIState s' l pl) (mkSMState v l').
  Proof.
    intros.
    eapply mem_bgflush_mem_bg_invariant with
        (I := fun s => invariant (mkLIState s l0 pl) /\ abstr (mkLIState s l0 pl) (mkSMState v l')); eauto.

    clear.
    unfold abstr; simpl; propositional; autorewrite with tso; intuition eauto.
    eapply AbsLockInvariant'.invariant_mem_bgflush; eauto.
    unfold invariant in *; simpl in *; propositional.
    destruct l'; (intuition idtac); autorewrite with tso; eauto.
    destruct (n == tid); subst; autorewrite with tso; eauto.
    destruct (pl == tid); subst; autorewrite with tso; eauto.
  Qed.

  Theorem mem_bg_preserves_abstr : forall s s' l pl l' v,
      invariant (mkLIState s l pl) ->
      abstr (mkLIState s l pl) (mkSMState v l') ->
      mem_bg s s' ->
      abstr (mkLIState s' l pl) (mkSMState v l').
  Proof.
    intros.
    eapply mem_bg_preserves_abstr' in H1; propositional; eauto.
  Qed.

  Definition absR := error_absR abstr.

  Lemma bg_invariant : forall T (op: Op T) tid s r s' evs,
      bg_step LockInvariantAPI.xstep invariant_step op tid s r s' evs ->
      invariant s /\
      LockInvariantAPI.xstep op tid s r s' evs /\
      invariant s'.
  Proof.
    intros.
    unfold bg_step, invariant_step in *; propositional; eauto.
  Qed.

  Lemma no_step_on_violation:
    forall (T : Type) (op : Op T) (tid : nat) (r : T) (evs : list event)
      s0 s',
      LockInvariantAPI.xstep op tid s0 r s' evs ->
      bad_lock op tid s0.(InvLock) ->
      False.
  Proof.
    unfold bad_lock.
    intros.
    invert H; eauto.
  Qed.

  Lemma step_any_op : forall T (op: Op T) tid evs,
      evs = match op with
            | Ext ev => [ev]
            | _ => nil
            end ->
      exists s r s',
        xstep op tid s r s' evs.
  Proof.
    subst; intros.
    destruct op; propositional; eauto using xstep.
    Grab Existential Variables.
    all: auto.
    constructor; auto.
  Qed.

  Lemma abstr_write_lock:
    forall tid pl s s',
      invariant {| InvValue := s; InvLock := None; PrevOwner := pl |} ->
      mem_read s Lock tid <> cLocked ->
      abstr {| InvValue := s; InvLock := None; PrevOwner := pl |}
            {| Value := s'.(Value); LockOwner := s'.(LockOwner) |} ->
      abstr {| InvValue := mem_flush (mem_write Lock cLocked s tid) tid;
               InvLock := Some tid;
               PrevOwner := tid |}
            {| Value := s'.(Value);
               LockOwner := Some tid |}.
  Proof.
    unfold abstr; simpl; propositional.
    intuition eauto.
    autorewrite with tso.
    unfold invariant in H; simpl in *.
    destruct (pl == tid); subst; eauto.
    (intuition idtac); autorewrite with tso in *; congruence.
  Qed.

  Lemma abstr_flush:
    forall (tid : nat) (s' : s) (l : option nat) (pl : nat) (s0 : memT addr nat),
      invariant {| InvValue := s0; InvLock := l; PrevOwner := pl |} ->
      abstr {| InvValue := s0; InvLock := l; PrevOwner := pl |}
            {| Value := s'.(Value); LockOwner := s'.(LockOwner) |} ->
      abstr {| InvValue := mem_flush s0 tid; InvLock := l; PrevOwner := pl |}
            {| Value := s'.(Value); LockOwner := l |}.
  Proof.
    unfold invariant, abstr; simpl; propositional.
    intuition eauto.
    destruct (pl == tid); subst; autorewrite with tso; eauto.
    destruct s'.(LockOwner); (intuition eauto); propositional; autorewrite with tso in *; eauto.
  Qed.

  Lemma abstr_clear:
    forall (tid : nat) (s3 : s) (v : memT addr nat),
      abstr {| InvValue := v; InvLock := Some tid; PrevOwner := tid |} s3 ->
      abstr
        {| InvValue := mem_write Lock cUnlocked v tid; InvLock := None; PrevOwner := tid |}
        {| Value := s3.(Value); LockOwner := None |}.
  Proof.
    destruct s3.
    unfold invariant, abstr; simpl; propositional; autorewrite with tso; eauto.
  Qed.

  Lemma abstr_write:
    forall (tid : nat) (s3 : s) (s1 : memT addr nat) (v' : nat),
      invariant {| InvValue := s1; InvLock := Some tid; PrevOwner := tid |} ->
      abstr {| InvValue := s1; InvLock := Some tid; PrevOwner := tid |} s3 ->
      abstr
        {| InvValue := mem_write Val v' s1 tid; InvLock := Some tid; PrevOwner := tid |}
        {| Value := v'; LockOwner := Some tid |}.
  Proof.
    unfold invariant, abstr; simpl; propositional; autorewrite with tso; eauto.
  Qed.

  Theorem absR_ok : op_abs absR LockInvariantAPI.l.(Layer.step) l.(Layer.step).
  Proof.
    unfold LockInvariantAPI.l, l, Layer.step, LockInvariantAPI.step, step, absR.
    hnf; intros.
    invert H0; clear H0;
      repeat match goal with
             | [ H: bg_step _ _ _ _ _ _ _ _ |- _ ] =>
               apply bg_invariant in H
             end; propositional.
    - invert H; clear H; eauto.
      destruct (decide_violation op tid s0.(InvLock)).
      + exfalso; eauto using no_step_on_violation.
      + invert H1.
        * (* TryAcquire, success *)
          exists (Valid (mkSMState s3.(Value) (Some tid)));
            intuition eauto.
          constructor.
          eapply mem_bg_preserves_abstr in H4; eauto.
          eapply AbsLockInvariant'.invariant_mem_bg in H0; eauto.
          eapply abstr_write_lock; eauto.
          constructor.
          destruct s3.
          unfold abstr in H4; simpl in *; propositional.
          constructor.
        * (* TryAcquire, failure *)
          exists (Valid (mkSMState s3.(Value) l0));
            intuition eauto.
          constructor.
          eapply mem_bg_preserves_abstr in H4; eauto.
          eapply AbsLockInvariant'.invariant_mem_bg in H0; eauto.
          eapply abstr_flush; eauto.
          constructor.
          destruct s3; simpl.
          unfold abstr in H4; simpl in *; propositional.
          constructor.
        * (* Clear *)
          assert (pl = tid).
          unfold invariant in H0; simpl in *; propositional.
          subst.
          exists (Valid (mkSMState s3.(Value) None));
            intuition eauto.
          constructor.
          eapply abstr_clear; eauto.
          constructor.
          destruct s3.
          unfold abstr in H4; simpl in *; propositional.
          constructor.
        * (* Read *)
          simpl in *.
          eapply mem_bg_preserves_abstr in H4; eauto.
          exists (Valid (mkSMState s3.(Value) (Some tid)));
            intuition eauto.
          constructor.
          replace s3.(LockOwner) with (Some tid) in H4; eauto.
          unfold abstr in H4; simpl in *; propositional; eauto.
          constructor.
          destruct s3.
          unfold abstr in H4; simpl in *; propositional.
          unfold invariant in H2; simpl in *; propositional.
          constructor.
        * (* Write *)
          simpl in *.
          destruct s3.
          assert (pl = tid).
          { unfold invariant in H0; simpl in *; propositional; auto. }
          assert (LockOwner0 = Some tid).
          { unfold abstr in H4; simpl in *; propositional. }
          subst.
          exists (Valid (mkSMState v' (Some tid)));
            intuition eauto.
          constructor.
          eapply abstr_write; eauto.
          constructor.
          constructor.
        * (* Ext *)
          exists (Valid s3); intuition eauto.
          constructor.
          constructor.

    - invert H; clear H.
      exists Error; intuition eauto.
      econstructor; eauto.
      unfold abstr in *; propositional; congruence.
    - invert H; clear H.
      exists Error; split; eauto.
      pose proof (@step_any_op _ op tid evs) as Hstep.
      invert H1; specialize (Hstep eq_refl); propositional; eauto.

      Grab Existential Variables.
      all: eauto.
  Qed.

  Theorem absInitP :
    forall s1,
      LockInvariantState.initP s1 ->
      exists s2 : State, absR s1 s2 /\ initP s2.
  Proof.
    unfold LockInvariantState.initP, absR, initP, SeqMemState.initP, abstr;
      propositional.
    eexists (Valid _); intuition eauto.
    constructor.
    simpl; eauto.
  Qed.

  Definition layerImplAbsT : LayerImplAbsT.t LockInvariantAPI.l SeqMemAPI.l.
    refine {| LayerImplAbsT.absR := absR;
              LayerImplAbsT.absR_ok := absR_ok;
              LayerImplAbsT.absInitP := absInitP;
           |}.
  Defined.

End AbsSeqMem'.


Module AbsSeqMem.
  Definition t : LayerImpl.t LockInvariantAPI.l SeqMemAPI.l.
    refine (LayerImplAbs.t AbsSeqMem'.layerImplAbsT).
  Defined.
End AbsSeqMem.

(** LAYER: TASLockAPI *)

Module LockOp.

  Inductive xOp : Type -> Type :=
  | Acquire : xOp bool
  | Release : xOp unit
  | Read : xOp nat
  | Write : nat -> xOp unit
  | Ext : event -> xOp unit
  .

  Definition Op := xOp.

End LockOp.

(** LAYER: RawLockAPI *)

Module RawLockAPI.

  Import LockOp.
  Import SeqMemState.

  Inductive xstep : OpSemantics Op s :=
  | StepAcquire : forall tid v,
      xstep Acquire tid (mkSMState v None) true (mkSMState v (Some tid)) nil
  | StepRelease : forall tid v l,
      xstep Release tid (mkSMState v l) tt (mkSMState v None) nil
  | StepRead : forall tid v l,
      xstep Read tid (mkSMState v l) v (mkSMState v l) nil
  | StepWrite : forall tid v0 v l,
      xstep (Write v) tid (mkSMState v0 l) tt (mkSMState v l) nil
  | StepExt : forall tid ev s,
      xstep (Ext ev) tid s tt s [ev]
  .

  Definition step := error_step xstep (fun T op tid s => match op with
                                                      | Acquire => False
                                                      | Ext _ => False
                                                      | _ => s.(LockOwner) <> Some tid
                                                      end).

  Definition initP := initP.
  
  Definition l : Layer.t Op State.
    refine {| Layer.step := step;
              Layer.initP := initP; |}.
  Defined.

End RawLockAPI.

Module LockImpl'.

  Definition acquire_cond (r : bool) := r.

  Definition once_cond {T} (r : T) :=
    true.

  Import TASOp.
  Import LockOp.

  Definition compile_op T (op : LockOp.Op T) : (option T -> TASOp.Op T) * (T -> bool) * option T :=
    match op with
    | Acquire => (fun _ => TryAcquire, acquire_cond, None)
    | Release => (fun _ => Clear, once_cond, None)
    | Read => (fun _ => TASOp.Read, once_cond, None)
    | Write v => (fun _ => TASOp.Write v, once_cond, None)
    | Ext ev => (fun _ => TASOp.Ext ev, once_cond, None)
    end.

  Ltac step_inv :=
    match goal with
    | H : SeqMemAPI.step _ _ _ _ _ _ |- _ =>
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
  Hint Resolve true.

  Theorem noop_or_success :
    noop_or_success compile_op SeqMemAPI.l.(Layer.step) RawLockAPI.l.(Layer.step).
  Proof.
    unfold RawLockAPI.l, Layer.step, noop_or_success.
    unfold RawLockAPI.step.
    intros.
    cut (match cond r with
            | false => s = s' /\ evs = []
            | true =>
              error_step RawLockAPI.xstep
                         (fun (T0 : Type) (op : Op T0) (tid0 : nat) (s0 : SeqMemState.s) =>
                            match op with
                            | Acquire => False
                            | Ext _ => False
                            | _ => s0.(SeqMemState.LockOwner) <> Some tid0
                            end) T opM tid s r s' evs
         end).
    destruct (cond r); eauto.

    destruct opM; simpl in *; repeat pair_inv;
        unfold acquire_cond, once_cond.
      all: invert H0;
        try match goal with
            | [ H: SeqMemAPI.xstep _ _ _ _ _ _ |- _ ] => invert H; clear H; eauto
            | [ H: bad_lock _ _ _ |- _ ] => unfold bad_lock in H; propositional
            end;
        destruct matches;
        eauto.

    Grab Existential Variables.
    all: auto.
  Qed.

  Definition initP_compat : forall s, SeqMemAPI.initP s -> RawLockAPI.initP s := ltac:(auto).
  
  Definition layerImplLoopT : LayerImplLoopT.t SeqMemAPI.l RawLockAPI.l.
    refine {| LayerImplLoopT.compile_op := compile_op;
              LayerImplLoopT.noop_or_success := noop_or_success;
              LayerImplLoopT.initP_compat := initP_compat; |}.
  Defined.
End LockImpl'.

Module LockImpl.
  Definition t : LayerImpl.t SeqMemAPI.l RawLockAPI.l.
    refine (LayerImplLoop.t LockImpl'.layerImplLoopT).
  Defined.
End LockImpl.

Module LockProtocol.

  Import LockOp.
  Import SeqMemState.

  Inductive xstep_allow : forall T, Op T -> nat -> s -> Prop :=
  | StepAcquire : forall tid s,
      xstep_allow Acquire tid s
  | StepRelease : forall tid v,
      xstep_allow Release tid (mkSMState v (Some tid))
  | StepRead : forall tid v,
      xstep_allow Read tid (mkSMState v (Some tid))
  | StepWrite : forall tid v0 v,
      xstep_allow (Write v) tid (mkSMState v0 (Some tid))
  | StepExt : forall tid ev s,
      xstep_allow (Ext ev) tid s
  .

  Definition step_allow T (op: Op T) tid s :=
    forall s', s = Valid s' ->
          xstep_allow op tid s'.

  Definition p : Protocol.t LockOp.Op SeqMemState.State.
    refine {| Protocol.step_allow := step_allow; |}.
  Defined.
End LockProtocol.


Module LockAPI.

  Definition step_allow := LockProtocol.step_allow.
  Definition step :=
    nilpotent_step RawLockAPI.step step_allow.

  Import LockOp.
  Import SeqMemState.

  Inductive step' : OpSemantics Op State :=
  | StepAcquire : forall tid v,
      step' Acquire tid
            (Valid (mkSMState v None))
            true
            (Valid (mkSMState v (Some tid))) nil
  | StepRelease : forall tid v,
      step' Release tid
            (Valid (mkSMState v (Some tid)))
            tt
            (Valid (mkSMState v None)) nil
  | StepRead : forall tid v,
      step' Read tid
            (Valid (mkSMState v (Some tid)))
            v
            (Valid (mkSMState v (Some tid))) nil
  | StepWrite : forall tid v v',
      step' (Write v') tid
            (Valid (mkSMState v (Some tid)))
            tt
            (Valid (mkSMState v' (Some tid))) nil
  | StepExt : forall tid ev s,
      step' (Ext ev) tid
            (Valid s)
            tt
            (Valid s)
            [ev]
  | StepError : forall tid T (op: Op T) r evs,
      evs = match op with
            | Ext ev => [ev]
            | _ => nil
                    end ->
      step' op tid Error r Error evs
  | StepNilpotent : forall tid T (op: Op T) v l r,
      match op with
      | Acquire => False
      | Ext _ => False
      | _ => l <> Some tid
      end ->
      step' op tid
            (Valid (mkSMState v l))
            r
            (Valid (mkSMState v l)) nil
  .


  Ltac cleanup :=
    repeat match goal with
           | [ H: Valid _ = Valid _ |- _ ] => invert H; clear H
           | [ H: Error = Valid _ |- _ ] => solve [ invert H ]
           | [ H: context[(mkSMState _ _).(LockOwner)] |- _ ] => simpl in H
           | [ H: Some ?tid <> Some ?tid |- _ ] => contradiction H
           | _ => progress propositional
           end.

  Ltac invertc H := invert H; clear H; cleanup; eauto.

  Hint Constructors step'.
  Hint Constructors LockProtocol.xstep_allow.

  Definition decide_invalid T (op: Op T) tid l :
    {match op with
     | Acquire => False
     | Ext _ => False
     | _ => l <> Some tid
     end} + {forall v, step_allow op tid (Valid (mkSMState v l))}.
  Proof.
    unfold step_allow, LockProtocol.step_allow.
    destruct op; simpl; eauto.
    - destruct (l == Some tid); subst; eauto.
      right; cleanup; eauto.
    - destruct (l == Some tid); subst; eauto.
      right; cleanup; eauto.
    - destruct (l == Some tid); subst; eauto.
      right; cleanup; eauto.
  Qed.

  Hint Resolve valid_step.

  Lemma step_allow_valid : forall T (op: Op T) tid s,
      step_allow op tid (Valid s) ->
      LockProtocol.xstep_allow op tid s.
  Proof.
    unfold step_allow; eauto.
  Qed.

  Lemma step_any_op : forall T (op: Op T) tid evs,
      evs = match op with
            | Ext ev => [ev]
            | _ => nil
            end ->
      exists s r s',
        RawLockAPI.xstep op tid s r s' evs.
  Proof.
    subst; intros.
    destruct op; propositional; eauto using RawLockAPI.xstep.
    Grab Existential Variables.
    all: auto.
    constructor; auto.
  Qed.

  Theorem step'_is_step : forall T (op: Op T) tid s r s' evs,
      step op tid s r s' evs <-> step' op tid s r s' evs.
  Proof.
    split; intros.
    - repeat match goal with
             | [ H: step _ _ _ _ _ _ |- _ ] => invertc H
             | [ H: step_allow _ _ _ |- _ ] => apply step_allow_valid in H
             | [ H: RawLockAPI.step _ _ _ _ _ _ |- _ ] => invertc H
             | [ H: RawLockAPI.xstep _ _ _ _ _ _ |- _ ] => invertc H
             | [ H: LockProtocol.xstep_allow _ _ _ |- _ ] => invertc H
             end.
      destruct s0; eauto.
      destruct s0.
      destruct (decide_invalid op tid LockOwner0); solve [ eauto || exfalso; eauto ].
      destruct op; eauto.
      exfalso; eapply H0.
      constructor.
    - hnf.
      unfold step_allow, LockProtocol.step_allow.
      destruct s0.
      + unfold RawLockAPI.step.
        invertc H; eauto 10;
          try solve [ left + right; (intuition cleanup); eauto ].
        right; (intuition eauto); cleanup.
        specialize (H _ eq_refl).
        invertc H.
      + invertc H.
        left; (intuition cleanup); eauto.
        pose proof (step_any_op op tid eq_refl); propositional.
        econstructor.
        eauto.
  Qed.

  Definition initP := initP.

  Definition l : Layer.t Op State.
     refine {| Layer.step := step;
               Layer.initP := initP; |}.
  Defined.

End LockAPI.

(** LAYER: LockedCounterAPI *)

Module CounterOp.

  Inductive xOp : Type -> Type :=
  | Inc : xOp nat
  | Dec : xOp nat
  | Ext : event -> xOp unit
  .

  Definition Op := xOp.

End CounterOp.


Module LockedCounterAPI.

  Import CounterOp.
  Import SeqMemState.

  Inductive xstep : forall T, Op T -> nat -> s -> T -> s -> list event -> Prop :=
  | StepInc : forall (tid: nat) v,
      xstep Inc tid (mkSMState v None) v (mkSMState (v+1) None) nil
  | StepDec : forall (tid: nat) v,
      xstep Dec tid (mkSMState v None) v (mkSMState (v-1) None) nil
  | StepExt : forall tid ev s,
      xstep (Ext ev) tid s tt s [ev]
  .

  Definition step := error_step xstep (fun T op tid s => False).

  Definition initP := initP.

  Definition l : Layer.t Op State.
     refine {| Layer.step := step;
               Layer.initP := initP; |}.
  Defined.
End LockedCounterAPI.

(** Using locks to get atomicity. *)

Module LockingCounter'.

  Import LockOp.
  Import CounterOp.

  Definition inc_core : proc LockOp.Op _ :=
    _ <- Call Acquire;
      v <- Call Read;
      _ <- Call (Write (v + 1));
      _ <- Call Release;
      Ret v.

  Definition dec_core : proc LockOp.Op _ :=
    _ <- Call Acquire;
      v <- Call Read;
      _ <- Call (Write (v - 1));
      _ <- Call Release;
      Ret v.

  Definition compile_op T (op : CounterOp.Op T)
    : proc LockOp.Op T :=
    match op with
    | Inc => inc_core
    | Dec => dec_core
    | Ext ev => Call (LockOp.Ext ev)
    end.

  Theorem compile_op_no_atomics : forall T (op : CounterOp.Op T),
      no_atomics (compile_op op).
  Proof.
    destruct op; econstructor; eauto.
  Qed.


  Hint Extern 1 (RawLockAPI.step _ _ _ _ _ _) => econstructor.
  Hint Extern 1 (LockAPI.step _ _ _ _ _ _) => left.
  Hint Extern 1 (LockAPI.step _ _ _ _ _ _) => right.
  Hint Extern 1 (LockAPI.step_allow _ _ _) => econstructor.
  Hint Extern 1 (LockedCounterAPI.step _ _ _ _ _ _) => econstructor.
  Hint Extern 1 (~ LockAPI.step_allow _ _ _) => intro H'; inversion H'.
  Hint Extern 1 (LockAPI.step_allow _ _ _ -> False) => intro H'; inversion H'.

  Ltac cleanup :=
    repeat match goal with
           | [ H: context[LockAPI.step] |- _ ] => setoid_rewrite LockAPI.step'_is_step in H
           | [ |- context[LockAPI.step] ] => setoid_rewrite LockAPI.step'_is_step
           | [ H: forall _, Valid _ = Valid _ -> _ |- _ ] =>
             specialize (H _ eq_refl)
           | [ H: context[(SeqMemState.mkSMState _ _).(SeqMemState.LockOwner)] |- _ ] =>
             simpl in H
           | [ |- _ /\ _ ] => split; [ solve [auto] | ]
           | [ |- _ /\ _ ] => split; [ | solve [auto] ]
           | _ => progress propositional
           end.

  Ltac invertc H := invert H; clear H; cleanup.
  Hint Constructors LockAPI.step'.

  Definition none_not_some A (v:A) : None <> Some v := ltac:(congruence).
  Hint Resolve none_not_some.

  Lemma acquire_right_mover :
    right_mover LockAPI.step Acquire.
  Proof.
    unfold right_mover; intros.
    cleanup.
    invertc H.
    - invertc H0; eauto.
      destruct op1; cleanup; eauto.
    - invertc H0; eauto.
  Qed.

  Definition some_not_eq A (x y:A) : x <> y -> Some x <> Some y := ltac:(congruence).
  Hint Resolve some_not_eq.

  Lemma release_left_mover :
    left_mover LockAPI.step Release.
  Proof.
    split.
    - eapply always_enabled_to_stable.
      unfold always_enabled, enabled_in; intros.
      cleanup.
      destruct s. destruct s. destruct (LockOwner == Some tid); subst.
      all: eauto 10.
    - unfold left_mover; intros.
      cleanup.
      invertc H.
      + invertc H0; eauto.
        destruct op0; cleanup; eauto.
      + invertc H0; eauto.
      + invertc H0; eauto.

        Grab Existential Variables.
        all: exact tt.
  Qed.

  Lemma read_right_mover :
    right_mover LockAPI.step Read.
  Proof.
    unfold right_mover; intros.
    cleanup.
    invertc H.
    - invertc H0; eauto.
    - invertc H0; eauto.
    - invertc H0; eauto.
  Qed.

  Lemma write_right_mover : forall v,
      right_mover LockAPI.step (Write v).
  Proof.
    unfold right_mover; intros.
    cleanup.
    invertc H.
    - invertc H0; eauto.
    - invertc H0; eauto.
    - invertc H0; eauto.
  Qed.

  Hint Resolve acquire_right_mover.
  Hint Resolve release_left_mover.
  Hint Resolve read_right_mover.
  Hint Resolve write_right_mover.

  Theorem ysa_movers : forall T (op : CounterOp.Op T),
      ysa_movers LockAPI.l.(Layer.step) (compile_op op).
  Proof.
    destruct op; unfold ysa_movers; simpl.
    - unfold inc_core; eauto 20.
    - unfold dec_core; eauto 20.
    - eauto.
  Qed.

  Ltac step_inv :=
    match goal with
    | [ H: LockAPI.step' _ _ _ _ _ _ |- _ ] => invertc H
    | |- LockedCounterAPI.step _ _ _ _ _ _ => hnf
    end.

  Hint Constructors LockedCounterAPI.xstep.

  Theorem compile_correct :
    compile_correct compile_op LockAPI.l.(Layer.step) LockedCounterAPI.l.(Layer.step).
  Proof.
    unfold Layer.step, LockAPI.l, LockedCounterAPI.l.
    unfold compile_correct; intros.
    destruct op.

    + repeat atomic_exec_inv.
      cleanup.
      repeat step_inv; simpl; eauto.
    + repeat atomic_exec_inv.
      cleanup.
      repeat step_inv; simpl; eauto.
    + repeat atomic_exec_inv.
      cleanup.
      repeat step_inv; simpl; eauto.

      Grab Existential Variables.
      all: auto.
      constructor; auto.
  Qed.

  Import SeqMemState.

  Theorem exec_others_preserves_lock' :
    forall tid ss ss',
      exec_others (restricted_step RawLockAPI.step LockAPI.step_allow) tid ss ss' ->
      (forall s, ss = Valid s -> LockOwner s = Some tid) ->
      (forall s', ss' = Valid s' -> LockOwner s' = Some tid).
  Proof.
    induction 1; (intuition eauto); propositional.
    invertc H3.
    repeat match goal with
           | [ H: RawLockAPI.step _ _ _ _ _ _ |- _ ] => invertc H
           | [ H: LockProtocol.xstep_allow _ _ _ |- _ ] => invertc H
           | [ H: RawLockAPI.xstep _ _ _ _ _ _ |- _ ] => invertc H
           | [ H: LockAPI.step_allow _ _ _ |- _ ] => apply LockAPI.step_allow_valid in H
           | _ => congruence
           end.
    specialize (IHclos_refl_trans_1n ltac:(congruence)).
    auto.
  Qed.

  Theorem exec_others_preserves_lock :
    forall tid s s',
      exec_others (restricted_step RawLockAPI.step LockAPI.step_allow) tid (Valid s) (Valid s') ->
      LockOwner s = Some tid ->
      LockOwner s' = Some tid.
  Proof.
    intros.
    eapply exec_others_preserves_lock' in H; eauto.
    intros; congruence.
  Qed.

  Lemma exec_others_preserves_error : forall tid s',
      exec_others (restricted_step RawLockAPI.step LockAPI.step_allow) tid Error s' ->
      s' = Error.
  Proof.
    intros.
    remember Error.
    induction H; propositional; eauto.
    invertc H1.
    invertc H3; eauto.
  Qed.

  Theorem step_allow_error : forall T (op: LockOp.Op T) tid,
      LockAPI.step_allow op tid Error.
  Proof.
    repeat (hnf; intros).
    congruence.
  Qed.

  Theorem step_allow_valid : forall T (op: LockOp.Op T) tid s,
      LockProtocol.xstep_allow op tid s ->
      LockAPI.step_allow op tid (Valid s).
  Proof.
    repeat (hnf; intros).
    invertc H0; eauto.
  Qed.

  Hint Resolve step_allow_error step_allow_valid.

  Ltac exec_propagate :=
    repeat match goal with
           | s : SeqMemState.State |- _ =>
             destruct s
           | H : exec_any _ _ _ (Call _) _ _ |- _ =>
             eapply exec_any_op in H; repeat deex
           | H: restricted_step _ _ _ _ _ _ _ _ |- _ => invertc H
           | H: RawLockAPI.step _ _ _ _ _ _ |- _ => invertc H
           | H: RawLockAPI.xstep _ _ _ _ _ _ |- _ => invertc H
           | H : exec_others _ _ (Valid _) (Valid _) |- _ =>
             eapply exec_others_preserves_lock in H; simpl in *; subst; [ | congruence ]
           | H : exec_others _ _ Error (Valid _) |- _ =>
             eapply exec_others_preserves_error in H; simpl in H; congruence
           | |- LockAPI.step_allow _ _ (Valid _) => apply step_allow_valid
           end.

  Lemma inc_follows_protocol : forall tid s,
      follows_protocol_proc RawLockAPI.step LockAPI.step_allow tid s inc_core.
  Proof.
    intros.
    repeat constructor.
    - repeat exec_propagate; eauto.
    - repeat exec_propagate; eauto.
    - repeat exec_propagate; eauto.
  Qed.

  Lemma dec_follows_protocol : forall tid s,
      follows_protocol_proc RawLockAPI.step LockAPI.step_allow tid s dec_core.
  Proof.
    intros.
    repeat constructor.
    - repeat exec_propagate; eauto.
    - repeat exec_propagate; eauto.
    - repeat exec_propagate; eauto.
  Qed.

  Lemma ext_follows_protocol : forall tid ev s,
      follows_protocol_proc RawLockAPI.step LockAPI.step_allow tid s (Call (LockOp.Ext ev)).
  Proof.
    intros.
    repeat constructor.
  Qed.

  Hint Resolve inc_follows_protocol.
  Hint Resolve dec_follows_protocol.
  Hint Resolve ext_follows_protocol.

  Theorem op_follows_protocol : forall tid s `(op : CounterOp.Op T),
      follows_protocol_proc RawLockAPI.l.(Layer.step) LockProtocol.p.(Protocol.step_allow) tid s (compile_op op).
  Proof.
    destruct op; simpl; eauto.
  Qed.

  Theorem allowed_stable :
    forall T (op : LockOp.Op T) `(op' : LockOp.Op T') tid tid' s s' r evs,
      tid <> tid' ->
      LockProtocol.p.(Protocol.step_allow) T op tid s ->
      LockAPI.l.(Layer.step) op' tid' s r s' evs ->
      LockProtocol.p.(Protocol.step_allow) T op tid s'.
  Proof.
    unfold LockAPI.l, Layer.step.
    unfold LockProtocol.p, Protocol.step_allow, LockProtocol.step_allow.
    intros.
    destruct op, op';
      repeat match goal with
             | [ H: LockAPI.step_allow _ _ (Valid _) |- _ ] =>
               apply LockAPI.step_allow_valid in H
             | [ H: LockProtocol.xstep_allow _ _ _ |- _ ] => invertc H
             | [ H: LockAPI.step _ _ _ _ _ _ |- _ ] => invertc H
             | [ H: RawLockAPI.step _ _ _ _ _ _ |- _ ] => invertc H
             | [ H: RawLockAPI.xstep _ _ _ _ _ _ |- _ ] => invertc H
             end; eauto.
   Qed.

  Theorem raw_step_ok :
    forall T (op : _ T) tid s r s' evs,
      restricted_step RawLockAPI.l.(Layer.step) LockProtocol.step_allow op tid s r s' evs ->
      LockAPI.l.(Layer.step) op tid s r s' evs.
  Proof.
    unfold RawLockAPI.l, LockAPI.l, Layer.step.
    eauto.
  Qed.

  Definition initP_compat : forall s, LockAPI.initP s -> LockedCounterAPI.initP s := ltac:(auto).
  Definition raw_initP_compat : forall s, RawLockAPI.initP s -> LockAPI.initP s := ltac:(auto).

  Definition layerImplMoversT : LayerImplMoversT.t LockAPI.l LockedCounterAPI.l.
    refine {| LayerImplMoversT.compile_op := compile_op;
              LayerImplMoversT.compile_op_no_atomics := compile_op_no_atomics;
              LayerImplMoversT.ysa_movers := ysa_movers;
              LayerImplMoversT.compile_correct := compile_correct;
              LayerImplMoversT.initP_compat := initP_compat; |}.
  Defined.

  Definition layerImplMoversProtocolT : LayerImplMoversProtocolT.t RawLockAPI.l LockAPI.l LockedCounterAPI.l LockProtocol.p.
    refine {| LayerImplMoversProtocolT.movers_impl := layerImplMoversT;
              LayerImplMoversProtocolT.op_follows_protocol := op_follows_protocol;
              LayerImplMoversProtocolT.allowed_stable := allowed_stable;
              LayerImplMoversProtocolT.raw_step_ok := raw_step_ok;
              LayerImplMoversProtocolT.raw_initP_compat := raw_initP_compat;
           |}.
  Defined.

End LockingCounter'.

(** LAYER: CounterAPI *)

Module CounterState.

  Definition State := nat.
  Definition initP (s : State) := s = 0.

End CounterState.

Module CounterAPI.

  Import CounterOp.
  Import CounterState.

  Inductive xstep : forall T, Op T -> nat -> State -> T -> State -> list event -> Prop :=
  | StepInc : forall tid v,
      xstep Inc tid v v (v + 1) nil
  | StepDec : forall tid v,
      xstep Dec tid v v (v - 1) nil
  | StepExt : forall tid ev s,
      xstep (Ext ev) tid s tt s [ev]
  .

  Definition step := xstep.

  Definition initP := initP.

  Definition l : Layer.t Op State.
     refine {| Layer.step := step;
               Layer.initP := initP; |}.
  Defined.
End CounterAPI.


(** Abstracting away the lock details. *)

Module AbsCounter'.

  Import SeqMemState.

  Definition absR (s1 : State) (s2 : CounterState.State) :=
    exists s, s1 = Valid s /\
         s.(LockOwner) = None /\
         s.(Value) = s2.

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

  Lemma step_ext : forall tid ev s r s',
      s = s' ->
      CounterAPI.step (CounterOp.Ext ev) tid s r s' [ev].
  Proof.
    propositional.
    destruct r.
    constructor.
  Qed.

  Hint Resolve step_inc step_dec step_ext.

  Ltac invertc H := invert H; clear H; propositional.

  Lemma absR_from_valid : forall s s2,
      s.(LockOwner) = None ->
      s2 = s.(Value) ->
      absR (Valid s) s2.
  Proof.
    unfold absR; intuition eauto.
  Qed.

  Hint Resolve absR_from_valid.

  Theorem absR_ok :
    op_abs absR LockedCounterAPI.l.(Layer.step) CounterAPI.l.(Layer.step).
  Proof.
    unfold op_abs; intros.
    unfold absR in * |-; propositional.
    invertc H0.
    invertc H6; simpl in *; eauto.
  Qed.

  Theorem absInitP :
    forall s1,
      SeqMemState.initP s1 ->
      exists s2, absR s1 s2 /\
      CounterState.initP s2.
  Proof.
    unfold absR, SeqMemState.initP, CounterState.initP; propositional.
    exists 0; eauto.
  Qed.

  Definition layerImplAbsT : LayerImplAbsT.t LockedCounterAPI.l CounterAPI.l.
    refine {| LayerImplAbsT.absR := absR;
              LayerImplAbsT.absR_ok := absR_ok;
              LayerImplAbsT.absInitP := absInitP;
           |}.
  Defined.
  
End AbsCounter'.

Module AbsCounter.
  Definition layerImplAbs : LayerImpl.t LockedCounterAPI.l CounterAPI.l.
    refine (LayerImplAbs.t AbsCounter'.layerImplAbsT).
  Defined.
End AbsCounter.

(** Linking *)

Module LockingCounter.
  Definition t: LayerImpl.t RawLockAPI.l LockedCounterAPI.l.
    refine (LayerImplMoversProtocol.t LockingCounter'.layerImplMoversProtocolT).
  Defined.
End LockingCounter.

Local Infix "<==>" := (Link.t) (at level 30, right associativity).

Module c.
  Definition t := AbsNondet.layerImplAbs
                    <==> TAS_TSOImpl.t
                    <==> AbsLockOwner.t
                    <==> AbsLockInvariant.t
                    <==> AbsSeqMem.t
                    <==> LockImpl.t
                    <==> LockingCounter.t
                    <==> AbsCounter.layerImplAbs.
End c.

Print Assumptions c.t.

Import CounterOp.

Definition test_thread :=
  Until
    (fun _ => false)
    (fun _ => _ <- Call Inc; _ <- Call Dec; Ret tt)
    None.

Definition test_threads : threads_state _ :=
  thread_from_list (repeat (existT _ _ test_thread) 16).

Definition compiled_threads : list (maybe_proc _) :=
  thread_to_list (c.t.(LayerImpl.compile_ts) test_threads).