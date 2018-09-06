Require Import CSPEC.
Require Import Helpers.Learn.
Require Import TSO.

Import ListNotations.

Global Set Implicit Arguments.
Global Generalizable All Variables.

Set Printing Projections.

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
    s = {| MemValue := fun a => 0; SBuf := fun _ => [] |}.

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

Module LockOwnerState <: State.

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
  | _ => l <> Some tid
  end.

Definition decide_violation T (op: TASOp.Op T) tid l :
  {bad_lock op tid l} + {match op with
                          | TASOp.TryAcquire => True
                          | _ => l = Some tid
                          end}.
Proof.
  destruct op, (l == Some tid); subst; eauto.
Qed.

Module LockOwnerAPI <: Layer TASOp LockOwnerState.

  Import TSOOp.
  Import TASOp.
  Import LockOwnerState.

  Inductive xstep : OpSemantics Op s :=
  | StepTryAcquireSuccess : forall tid s s' l,
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
  (* | StepFlush : forall tid s s' l,
      mem_bg s s' ->
      xstep Flush tid
            (mkLOState s l)
            tt
            (mkLOState (mem_flush s' tid) l)
            nil *)
  .

  Definition step := error_step xstep (fun T op tid s => bad_lock op tid s.(TASLock)).

End LockOwnerAPI.


Module AbsLockOwner' <: LayerImplAbsT
                          TASOp
                          TSOState TAS_TSOAPI
                          LockOwnerState LockOwnerAPI.
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

  Theorem absR_ok : op_abs absR TAS_TSOAPI.step step.
  Proof.
    unfold step.
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

Module LockInvariantState <: State.

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

Definition only_val (sbuf: list (TSOOp.addr * nat)) :=
  List.Forall (fun '(a, _) => a = TSOOp.Val) sbuf.

Definition unlock_last (sbuf: list (TSOOp.addr * nat)) :=
  exists l, sbuf = (TSOOp.Lock, TSOOp.cUnlocked) :: l /\
       only_val l.

Module LockInvariantAPI <: Layer TASOp LockInvariantState.

  Import TSOOp.
  Import TASOp.
  Import LockInvariantState.

  Definition invariant (s:LockInvariantState.s) :=
    match s.(InvLock) with
    | Some tid => empty_sb_except s.(InvValue) tid /\
                 s.(PrevOwner) = tid /\
                 only_val (s.(InvValue).(SBuf) tid)
    | None => (s.(InvValue).(MemValue) Lock <> cLocked /\
              empty_sb s.(InvValue)) \/
             (s.(InvValue).(MemValue) Lock = cLocked /\
              empty_sb_except s.(InvValue) s.(PrevOwner) /\
              unlock_last (s.(InvValue).(SBuf) s.(PrevOwner)))
    end.

  Inductive xstep : OpSemantics Op s :=
  | StepTryAcquireSuccess : forall tid s s' l pl,
      mem_bg s s' ->
      mem_read s' Lock tid <> cLocked ->
      xstep TryAcquire tid
            (mkLIState s l pl)
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
  .

  Definition invariant_step (s1 s2:s) :=
    invariant s1 /\ s2 = s1.

  Definition step := error_step
                       (bg_step xstep invariant_step)
                       (fun T op tid s => bad_lock op tid s.(InvLock)).
End LockInvariantAPI.

Inductive error_absR {State1 State2} {absR: State1 -> State2 -> Prop} :
  OrError State1 -> OrError State2 -> Prop :=
| absR_error : error_absR Error Error
| absR_valid : forall s1 s2,
    absR s1 s2 ->
    error_absR (Valid s1) (Valid s2).

Arguments error_absR {State1 State2} absR.

Hint Constructors error_absR.

Module AbsLockInvariant' <: LayerImplAbsT
                              TASOp
                              LockOwnerState LockOwnerAPI
                              LockInvariantState LockInvariantAPI.
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
    induction l; simpl; intros; eauto.
    rewrite IHl.
    simpl.
    destruct_with_eqn (l ++ a0 :: l'); auto.
    apply app_eq_nil in Heql0; intuition congruence.
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

  Theorem invariant_mem_bg : forall s s' l pl,
      invariant (mkLIState s l pl) ->
      mem_bg s s' ->
      invariant (mkLIState s' l pl).
  Proof.
    unfold invariant; simpl; intuition eauto.
    destruct l; intuition eauto.
    eapply empty_sb_mem_bg_noop in H0; eauto; subst; eauto.
  Admitted.

  Theorem invariant_mem_flush : forall s s' l pl tid,
      invariant (mkLIState s l pl) ->
      s' = mem_flush s tid ->
      invariant (mkLIState s' l pl).
  Proof.
  Admitted.

  Theorem invariant_write_lock : forall s tid l pl,
      invariant (mkLIState s l pl) ->
      mem_read s Lock tid <> cLocked ->
      invariant (mkLIState
                   (mem_flush (mem_write Lock cLocked s tid) tid)
                   (Some tid)
                   tid).
  Proof.
    unfold invariant; simpl; propositional.
    autorewrite with fupd.
  Admitted.

  Lemma invariant_write_unlock : forall s tid pl,
      invariant (mkLIState s (Some tid) pl) ->
      invariant (mkLIState (mem_write Lock cUnlocked s tid) None pl).
  Proof.
    unfold invariant; simpl; propositional.
  Admitted.

  Lemma invariant_write_val : forall s v tid pl,
      invariant (mkLIState s (Some tid) pl) ->
      invariant (mkLIState (mem_write Val v s tid) (Some tid) pl).
  Proof.
    unfold invariant; simpl; propositional.
  Admitted.

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

  Theorem absR_ok : op_abs absR LockOwnerAPI.step step.
  Proof.
    unfold LockOwnerAPI.step, step, absR.
    hnf; intros.
    invert H0; clear H0.
    - invert H; clear H; eauto.
      destruct (decide_violation op tid s0.(TASLock)).
      + exfalso.
        eauto using no_step_on_violation.
      + unfold abstr in * |- .
        destruct s3; simpl in *; propositional.
        invert H6; simpl in *.
        * eexists; split; [ eapply abstr_intro with (pl:=tid) | ].
          eapply invariant_mem_bg in H1; eauto.
          eapply invariant_write_lock; eauto.
          constructor.
          apply bg_invariant; eauto.
          eapply invariant_mem_bg in H1; eauto.
          eapply invariant_write_lock; eauto.
        * eexists; split; [ eapply abstr_intro with (pl:=PrevOwner0) | ].
          eapply invariant_mem_bg in H10; eauto.
          eapply invariant_mem_flush; eauto.
          constructor.
          apply bg_invariant; eauto.
          eapply invariant_mem_bg in H10; eauto.
          eapply invariant_mem_flush; eauto.
        * eexists; split; [ eapply abstr_intro with (pl := PrevOwner0) | ].
          eapply invariant_write_unlock; eauto.
          constructor.
          apply bg_invariant; eauto.
          eapply invariant_write_unlock; eauto.
        * eexists; split; [ eapply abstr_intro with (pl := PrevOwner0) | ].
          eapply invariant_mem_bg; eauto.
          constructor.
          apply bg_invariant; eauto.
          eapply invariant_mem_bg; eauto.
        * eexists; split; [ eapply abstr_intro with (pl := PrevOwner0) | ].
          eapply invariant_write_val; eauto.
          constructor.
          apply bg_invariant; eauto.
          eapply invariant_write_val; eauto.
    - invert H.
      exists Error; intuition eauto.
      econstructor.
      erewrite abstr_lock_same by eauto; eauto.
    - invert H; clear H.
      exists Error; split; eauto.
      admit. (* TODO: show some execution exists for Error -> Error *)
  Admitted.

  Theorem absInitP :
    forall s1,
      LockOwnerState.initP s1 ->
      exists s2 : State, absR s1 s2 /\ initP s2.
  Proof.
    unfold LockOwnerState.initP, initP; propositional.
    exists_econstructor; intuition eauto.
    constructor.
    unfold abstr; intuition eauto.
    hnf; simpl; eauto.
    left.
    intuition eauto.
    unfold empty_sb; intros; eauto.
  Qed.

End AbsLockInvariant'.

Module AbsLockInvariant := LayerImplAbs
                              TASOp
                              LockOwnerState LockOwnerAPI
                              LockInvariantState LockInvariantAPI
                              AbsLockInvariant'.


Module SeqMemState <: State.

  Record s := mkSMState {
                  Value : nat;
                  LockOwner : option nat;
                }.

  Definition State := OrError s.

  Definition initP s :=
    s = Valid {| Value := 0; LockOwner := None |}.
End SeqMemState.


Module SeqMemAPI <: Layer TASOp SeqMemState.

  Import TASOp.
  Import SeqMemState.

  Inductive xstep : OpSemantics Op s :=
  | StepTryAcquireSuccess : forall tid v l,
      xstep TryAcquire tid (mkSMState v l) true (mkSMState v (Some tid)) nil
  | StepTryAcquireFail : forall tid v l,
      xstep TryAcquire tid (mkSMState v l) false (mkSMState v l) nil
  | StepClear : forall tid v,
      xstep Clear tid (mkSMState v (Some tid)) tt (mkSMState v None) nil
  | StepRead : forall tid v,
      xstep Read tid (mkSMState v (Some tid)) v (mkSMState v (Some tid)) nil
  | StepWrite : forall tid v v',
      xstep (Write v') tid (mkSMState v (Some tid)) tt (mkSMState v' (Some tid)) nil
  .

  Definition step := error_step xstep (fun T op tid s => bad_lock op tid s.(LockOwner)).
End SeqMemAPI.


Module AbsSeqMem' <: LayerImplAbsT
                       TASOp
                       LockInvariantState LockInvariantAPI
                       SeqMemState SeqMemAPI.

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

  Theorem mem_bg_preserves_abstr : forall s s' l pl l' v,
      abstr (mkLIState s l pl) (mkSMState v l') ->
      mem_bg s s' ->
      abstr (mkLIState s' l pl) (mkSMState v l').
  Proof.
  Admitted.

  Definition absR := error_absR abstr.

  Import LockInvariantAPI.
  Import SeqMemAPI.

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

  Theorem absR_ok : op_abs absR LockInvariantAPI.step step.
  Proof.
    unfold LockInvariantAPI.step, step, absR.
    hnf; intros.
    invert H0; clear H0;
      repeat match goal with
             | [ H: bg_step _ _ _ _ _ _ _ _ |- _ ] =>
               apply bg_invariant in H
             end; propositional.
    - invert H; clear H; eauto.
      destruct (decide_violation op tid s0.(InvLock)).
      + exfalso; eauto using no_step_on_violation.
      + eexists (Valid _); intuition eauto.
        constructor.
        * admit.
        * econstructor; eauto.
          admit.
    - invert H; clear H.
      exists Error; intuition eauto.
      econstructor; eauto.
      unfold abstr in *; propositional; congruence.
    - invert H; clear H.
      exists Error; split; eauto.
      econstructor.
      admit. (* TODO: show some execution *)
  Admitted.

  Theorem absInitP :
    forall s1,
      LockInvariantState.initP s1 ->
      exists s2 : State, absR s1 s2 /\ initP s2.
  Proof.
  Admitted.

End AbsSeqMem'.


Module AbsSeqMem := LayerImplAbs
                      TASOp
                      LockInvariantState LockInvariantAPI
                      SeqMemState SeqMemAPI
                      AbsSeqMem'.

(** LAYER: TASLockAPI *)

Module LockOp <: Ops.

  Inductive xOp : Type -> Type :=
  | Acquire : xOp bool
  | Release : xOp unit
  | Read : xOp nat
  | Write : nat -> xOp unit.

  Definition Op := xOp.

End LockOp.

(** LAYER: RawLockAPI *)

Module RawLockAPI <: Layer LockOp SeqMemState.

  Import LockOp.
  Import SeqMemState.

  Inductive xstep : OpSemantics Op s :=
  | StepAcquire : forall tid v,
      (* TODO: TryAcquire must start from l = None in order to succeed *)
      xstep Acquire tid (mkSMState v None) true (mkSMState v (Some tid)) nil
  | StepRelease : forall tid v l,
      xstep Release tid (mkSMState v l) tt (mkSMState v None) nil
  | StepRead : forall tid v l,
      xstep Read tid (mkSMState v l) v (mkSMState v l) nil
  | StepWrite : forall tid v0 v l,
      xstep (Write v) tid (mkSMState v0 l) tt (mkSMState v l) nil
  .

  Definition step := error_step xstep (fun T op tid s => match op with
                                                      | Acquire => False
                                                      | _ => s.(LockOwner) <> Some tid
                                                      end).

End RawLockAPI.

Module LockImpl' <:
  LayerImplLoopT
    SeqMemState
    TASOp  SeqMemAPI
    LockOp RawLockAPI.

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
    noop_or_success compile_op SeqMemAPI.step RawLockAPI.step.
  Proof.
    unfold noop_or_success.
    unfold RawLockAPI.step.
    intros.
    cut (match cond r with
            | false => s = s' /\ evs = []
            | true =>
              error_step RawLockAPI.xstep
                         (fun (T0 : Type) (op : Op T0) (tid0 : nat) (s0 : SeqMemState.s) =>
                            match op with
                            | Acquire => False
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
      admit. (* propagate TryAcquire None *)

    Grab Existential Variables.
    all: auto.
  Admitted.

End LockImpl'.

Module LockImpl :=
  LayerImplLoop
    SeqMemState
    TASOp  SeqMemAPI
    LockOp RawLockAPI
    LockImpl'.

Module LockProtocol <: Protocol LockOp SeqMemState.

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
  .

  Definition step_allow T (op: Op T) tid s :=
    exists s', s = Valid s' /\
          xstep_allow op tid s'.

End LockProtocol.


Module LockAPI <: Layer LockOp SeqMemState.

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
  | StepError : forall tid T (op: Op T) r,
      (* TODO: for Ext allow an event *)
      step' op tid Error r Error nil
  | StepNilpotent : forall tid T (op: Op T) v l r,
      match op with
      | Acquire => False
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
     | _ => l <> Some tid
     end} + {forall v, step_allow op tid (Valid (mkSMState v l))}.
  Proof.
    unfold step_allow, LockProtocol.step_allow.
    destruct op; simpl; eauto.
    - destruct (l == Some tid); subst; eauto.
    - destruct (l == Some tid); subst; eauto.
    - destruct (l == Some tid); subst; eauto.
  Qed.

  Hint Resolve valid_step.

  Theorem step'_is_step : forall T (op: Op T) tid s r s' evs,
      step op tid s r s' evs <-> step' op tid s r s' evs.
  Proof.
    split; intros.
    - repeat match goal with
             | [ H: step _ _ _ _ _ _ |- _ ] => invertc H
             | [ H: step_allow _ _ _ |- _ ] => invertc H
             | [ H: RawLockAPI.step _ _ _ _ _ _ |- _ ] => invertc H
             | [ H: RawLockAPI.xstep _ _ _ _ _ _ |- _ ] => invertc H
             | [ H: LockProtocol.xstep_allow _ _ _ |- _ ] => invertc H
             end.
      destruct s0; eauto.
      destruct s0.
      destruct (decide_invalid op tid LockOwner0); solve [ eauto || exfalso; eauto ].
    - hnf.
      unfold step_allow, LockProtocol.step_allow.
      destruct s0.
      + unfold RawLockAPI.step.
        invertc H; eauto 10.
        right; (intuition eauto); cleanup.
        invertc H0.
      + invertc H.
        right; (intuition eauto); cleanup.
  Qed.

End LockAPI.

(** LAYER: LockedCounterAPI *)

Module CounterOp <: Ops.

  Inductive xOp : Type -> Type :=
  | Inc : xOp nat
  | Dec : xOp nat.

  Definition Op := xOp.

End CounterOp.


Module LockedCounterAPI <: Layer CounterOp SeqMemState.

  Import CounterOp.
  Import SeqMemState.

  Inductive xstep : forall T, Op T -> nat -> s -> T -> s -> list event -> Prop :=
  | StepInc : forall (tid: nat) v,
      xstep Inc tid (mkSMState v None) v (mkSMState (v+1) None) nil
  | StepDec : forall (tid: nat) v,
      xstep Dec tid (mkSMState v None) v (mkSMState (v-1) None) nil
  .

  Definition step := error_step xstep (fun T op tid s => False).

End LockedCounterAPI.

(** Using locks to get atomicity. *)

Module LockingCounter' <:
  LayerImplMoversProtocolT
    SeqMemState
    LockOp    RawLockAPI LockAPI
    CounterOp LockedCounterAPI
    LockProtocol.

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
    - invertc H0.
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
      + invertc H0.
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
    - invertc H0.
      destruct op1; cleanup; eauto.
    - invertc H0; eauto.
    - invertc H0; eauto.
  Qed.

  Lemma write_right_mover : forall v,
      right_mover LockAPI.step (Write v).
  Proof.
    unfold right_mover; intros.
    cleanup.
    invertc H.
    - invertc H0.
      destruct op1; cleanup; eauto.
    - invertc H0; eauto.
    - invertc H0; eauto.
  Qed.

  Hint Resolve acquire_right_mover.
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

  Ltac step_inv :=
    match goal with
    | [ H: LockAPI.step' _ _ _ _ _ _ |- _ ] => invertc H
    | |- LockedCounterAPI.step _ _ _ _ _ _ => hnf
    end.

  Hint Constructors LockedCounterAPI.xstep.

  Theorem compile_correct :
    compile_correct compile_op LockAPI.step LockedCounterAPI.step.
  Proof.
    unfold compile_correct; intros.
    destruct op.

    + repeat atomic_exec_inv.
      cleanup.
      repeat step_inv; simpl; eauto.
    + repeat atomic_exec_inv.
      cleanup.
      repeat step_inv; simpl; eauto.

      Grab Existential Variables.
      all: auto.
  Qed.

  Import SeqMemState.

  Theorem exec_others_preserves_lock :
    forall tid s s',
      exec_others (restricted_step RawLockAPI.step LockAPI.step_allow) tid (Valid s) (Valid s') ->
      LockOwner s = Some tid ->
      LockOwner s' = Some tid.
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
