Require Import Helpers.Helpers.
Require Import Helpers.ListStuff.
Require Import Helpers.Maps.
Require Import ConcurProc.
Require Import Equiv.
Require Import Omega.
Require Import List.
Require Import Modules.
Require Import Ordering.
Require Import Abstraction.
Require Import Movers.
Require Import Compile.
Require Import CompileLoop.
Require Import Protocol.

Import ListNotations.

Global Set Implicit Arguments.
Global Generalizable All Variables.


Section HorizontalComposition.

  Variable indexT : Type.
  Context {cmp : Ordering indexT}.
  Variable indexValid : indexT -> Prop.

  Variable sliceOpT : Type -> Type.
  Variable sliceState : Type.
  Variable sliceStep : OpSemantics sliceOpT sliceState.
  Variable initP : sliceState -> Prop.

  Inductive horizOpT : Type -> Type :=
  | Slice : forall (i : indexT) T (op : sliceOpT T), horizOpT T
  .

  Definition horizState := FMap.t indexT sliceState.

  Inductive horizStep :
      forall T, horizOpT T -> nat -> horizState -> T -> horizState -> list event -> Prop :=
  | StepSlice :
    forall tid idx (S : horizState) (s : sliceState) `(op : sliceOpT T) r s' evs,
      FMap.MapsTo idx s S ->
      sliceStep op tid s r s' evs ->
      horizStep (Slice idx op) tid S r (FMap.add idx s' S) evs
  .

  Definition horizInitP (S : horizState) :=
    forall i,
      indexValid i ->
      exists s,
        FMap.MapsTo i s S /\
        initP s.

  Fixpoint SliceProc (i : indexT) `(p : proc sliceOpT T) : proc horizOpT T :=
    match p with
    | Op op => Op (Slice i op)
    | Ret v => Ret v
    | Bind p1 p2 => Bind (SliceProc i p1) (fun r => SliceProc i (p2 r))
    | Until cond p init => Until cond (fun x => SliceProc i (p x)) init
    | Atomic p => Atomic (SliceProc i p)
    end.

End HorizontalComposition.

Arguments horizState indexT {cmp} sliceState.
Arguments horizStep indexT {cmp sliceOpT sliceState} sliceStep.
Arguments Slice {indexT sliceOpT} i {T}.


Section HorizontalCompositionAbs.

  Variable indexT : Type.
  Context {cmp : Ordering indexT}.

  Variable sliceOpT : Type -> Type.

  Variable sliceState1 : Type.
  Variable sliceStep1 : OpSemantics sliceOpT sliceState1.

  Variable sliceState2 : Type.
  Variable sliceStep2 : OpSemantics sliceOpT sliceState2.


  Variable absR : sliceState1 -> sliceState2 -> Prop.

  Definition horizAbsR (S1 : horizState indexT sliceState1) (S2 : horizState indexT sliceState2) : Prop :=
    forall (i : indexT),
      ( forall s1,
          FMap.MapsTo i s1 S1 ->
            exists s2, FMap.MapsTo i s2 S2 /\ absR s1 s2 ) /\
      ( forall s2,
          FMap.MapsTo i s2 S2 ->
            exists s1, FMap.MapsTo i s1 S1 /\ absR s1 s2 ).

  Hint Resolve FMap.add_mapsto.
  Hint Resolve FMap.mapsto_add_ne'.

  Theorem horizAbsR_ok :
    op_abs absR sliceStep1 sliceStep2 ->
    op_abs horizAbsR (horizStep indexT sliceStep1) (horizStep indexT sliceStep2).
  Proof.
    unfold op_abs, horizAbsR; intros.
    inversion H1; clear H1; subst; repeat sigT_eq.
    eapply H0 in H5; deex.
    eapply H in H8; eauto; deex.
    eexists; split; [ | econstructor; eauto ].
    intros.
    destruct (i == idx); subst.
    - split; intros.
      + eapply FMap.mapsto_add_eq in H5; subst; eauto.
      + eapply FMap.mapsto_add_eq in H5; subst; eauto.
    - specialize (H0 i); intuition idtac.
      + eapply FMap.mapsto_add_ne in H0; eauto.
        specialize (H5 _ H0); deex; eauto.
      + eapply FMap.mapsto_add_ne in H0; eauto.
        specialize (H6 _ H0); deex; eauto.
  Qed.


  Variable indexValid : indexT -> Prop.
  Variable initP1 : sliceState1 -> Prop.
  Variable initP2 : sliceState2 -> Prop.

  Variable initP_ok :
    forall s1 s2,
      initP1 s1 ->
      absR s1 s2 ->
      initP2 s2.

  Theorem horizAbsR_initP_ok :
    forall s1 s2,
      horizInitP indexValid initP1 s1 ->
      horizAbsR s1 s2 ->
      horizInitP indexValid initP2 s2.
  Proof.
    unfold horizInitP, horizAbsR; intros.
    specialize (H _ H1); deex.
    eapply H0 in H; deex.
    eapply initP_ok in H2; eauto.
  Qed.

End HorizontalCompositionAbs.

Arguments horizAbsR indexT {cmp sliceState1 sliceState2} absR.


Section HorizontalCompositionMovers.

  Variable indexT : Type.
  Context {cmp : Ordering indexT}.

  Variable sliceOpT : Type -> Type.
  Variable sliceState : Type.
  Variable sliceStep : OpSemantics sliceOpT sliceState.

  Hint Resolve FMap.add_mapsto.
  Hint Resolve FMap.mapsto_add_ne'.

  Theorem horiz_right_mover_ok :
    forall `(op : sliceOpT T),
      right_mover sliceStep op ->
      forall i,
        right_mover (horizStep indexT sliceStep) (Slice i op).
  Proof.
    intros.
    unfold right_mover; intros.
    inversion H0; clear H0; subst; repeat sigT_eq.
    eapply H in H10 as H'; intuition subst.
    inversion H3; clear H3; subst; repeat sigT_eq.
    destruct (i == idx); subst.
    - eapply FMap.mapsto_add in H6; subst.
      eapply H1 in H11; eauto; deex.
      eexists; split.
      + econstructor; eauto.
      + rewrite FMap.add_add.
        erewrite <- FMap.add_add with (v1 := s'0).
        econstructor; eauto.
    - eapply FMap.mapsto_add_ne in H6; eauto.
      eexists; split.
      + econstructor; eauto.
      + rewrite FMap.add_add_ne by eauto.
        econstructor; eauto.
  Qed.

  Theorem horiz_enabled_stable :
    forall `(op : sliceOpT T),
      enabled_stable sliceStep T op ->
      forall i,
        enabled_stable (horizStep indexT sliceStep) T (Slice i op).
  Proof.
    intros.
    unfold enabled_stable; intros.
    unfold enabled_in in *; repeat deex.
    inversion H1; clear H1; subst; repeat sigT_eq.
    inversion H2; clear H2; subst; repeat sigT_eq.
    destruct (i == idx); subst.
    - replace s0 with s1 in * by ( eapply FMap.mapsto_unique; eauto ).
      edestruct H.
      2: unfold enabled_in; eauto.
      2: eauto.
      eauto.
      repeat deex.
      do 3 eexists. econstructor; eauto.
    - do 3 eexists. econstructor; eauto.
  Qed.

  Theorem horiz_left_mover_ok :
    forall `(op : sliceOpT T),
      left_mover sliceStep op ->
      forall i,
        left_mover (horizStep indexT sliceStep) (Slice i op).
  Proof.
    intros.
    split; intros.
    - eapply horiz_enabled_stable.
      destruct H; eauto.
    - inversion H0; clear H0; subst; repeat sigT_eq.
      eapply H in H10 as H'; intuition subst.
      inversion H3; clear H3; subst; repeat sigT_eq.
      destruct (i == idx); subst.
      * eapply FMap.mapsto_add in H7; subst.
        eapply H1 in H11; eauto; deex.
        eexists; split.
        + econstructor; eauto.
        + rewrite FMap.add_add.
          erewrite <- FMap.add_add with (v1 := s').
          econstructor; eauto.
      * eapply FMap.mapsto_add_ne in H7; eauto.
        eexists; split.
        + econstructor; eauto.
        + rewrite FMap.add_add_ne by eauto.
          econstructor; eauto.
  Qed.

  Theorem horiz_left_mover_pred_ok :
    forall `(op : sliceOpT T) P,
      left_mover_pred sliceStep op P ->
      forall i,
        left_mover_pred (horizStep indexT sliceStep) (Slice i op)
          (fun tid S => forall s, FMap.MapsTo i s S -> P tid s).
  Proof.
    intros.
    split; intros.
    - eapply horiz_enabled_stable.
      destruct H; eauto.
    - inversion H0; clear H0; subst; repeat sigT_eq.
      eapply H in H10 as H'; intuition subst.
      inversion H4; clear H4; subst; repeat sigT_eq.
      destruct (i == idx); subst.
      * eapply FMap.mapsto_add in H7; subst.
        eapply H1 in H12; eauto; deex.
        eexists; split.
        + econstructor; eauto.
        + rewrite FMap.add_add.
          erewrite <- FMap.add_add with (v1 := s').
          econstructor; eauto.
      * eapply FMap.mapsto_add_ne in H7; eauto.
        eexists; split.
        + econstructor; eauto.
        + rewrite FMap.add_add_ne by eauto.
          econstructor; eauto.
  Qed.

  Hint Resolve horiz_right_mover_ok.
  Hint Resolve horiz_left_mover_ok.
  Hint Resolve horiz_left_mover_pred_ok.


  Lemma exec_others_preserves_slice :
    forall S1 S2 tid,
      exec_others (horizStep indexT sliceStep) tid S1 S2 ->
      forall i s2,
        FMap.MapsTo i s2 S2 ->
        exists s1,
          FMap.MapsTo i s1 S1.
  Proof.
    induction 1; intros; eauto.
    eapply IHclos_refl_trans_1n in H1.
    repeat deex.
    inversion H2; clear H2; subst; repeat sigT_eq.
    destruct (i == idx); subst; eauto.
    eapply FMap.mapsto_add_ne in H1; eauto.
  Qed.

  Hint Resolve FMap.mapsto_add_ne.

  Lemma atomic_exec_preserves_slice :
    forall S1 S2 tid `(p : proc _ T) r evs,
      atomic_exec (horizStep indexT sliceStep) p tid S1 r S2 evs ->
      forall i s2,
        FMap.MapsTo i s2 S2 ->
        exists s1,
          FMap.MapsTo i s1 S1.
  Proof.
    induction 1; intros; eauto.
    - eapply IHatomic_exec2 in H1; repeat deex; eauto.
    - inversion H; clear H; subst; repeat sigT_eq.
      destruct (i == idx); subst; eauto.
  Qed.

  Lemma exec_any_preserves_slice :
    forall S1 S2 tid `(p : proc _ T) r,
      exec_any (horizStep indexT sliceStep) tid S1 p r S2 ->
      forall i s2,
        FMap.MapsTo i s2 S2 ->
        exists s1,
          FMap.MapsTo i s1 S1.
  Proof.
    induction 1; intros; eauto.
    - eapply IHexec_any in H2; repeat deex.
      inversion H0; clear H0; subst; repeat sigT_eq.
      destruct (i == idx); subst; eauto.
    - inversion H; clear H; subst; repeat sigT_eq; eauto.
      + inversion H7; clear H7; subst; repeat sigT_eq.
        destruct (i == idx); subst; eauto.
      + eapply atomic_exec_preserves_slice in H7; eauto.
    - eapply IHexec_any in H1; repeat deex.
      clear IHexec_any H0.
      generalize dependent H.
      generalize dependent H1.
      generalize (@inr T _ p').
      clear; intros.
      induction H; eauto.
      + inversion H; clear H; subst; repeat sigT_eq.
        destruct (i == idx); subst; eauto.
      + eapply atomic_exec_preserves_slice in H; eauto.
  Qed.

  Lemma exec_any_slice :
    forall S1 S2 tid `(p : proc _ T) r,
      exec_any (horizStep indexT sliceStep) tid S1 p r S2 ->
      forall `(op : sliceOpT T) i s1 s2,
        p = Op (Slice i op) ->
        FMap.MapsTo i s1 S1 ->
        FMap.MapsTo i s2 S2 ->
          exec_any sliceStep tid s1 (Op op) r s2.
  Proof.
    induction 1; intros; subst.
    - inversion H0; clear H0; subst; repeat sigT_eq.
      destruct (i == idx); subst; eauto.
      replace s3 with s1 in * by ( eapply FMap.mapsto_unique; eauto ).
      eapply ExecAnyOther; eauto.
    - inversion H; clear H; subst; repeat sigT_eq.
      inversion H8; clear H8; subst; repeat sigT_eq.
      replace s1 with s0 in * by ( eapply FMap.mapsto_unique; eauto ).
      eapply FMap.mapsto_add in H2; subst.
      eauto.
    - inversion H.
  Unshelve.
    all: eauto.
  Qed.

  Lemma exec_others_slice :
    forall S1 S2 tid,
      exec_others (horizStep indexT sliceStep) tid S1 S2 ->
      forall s1 s2 i,
        FMap.MapsTo i s1 S1 ->
        FMap.MapsTo i s2 S2 ->
          exec_others sliceStep tid s1 s2.
  Proof.
    induction 1; intros; eauto.
    - replace s2 with s1 in * by ( eapply FMap.mapsto_unique; eauto ).
      eauto.
    - repeat deex.
      inversion H3; clear H3; subst; repeat sigT_eq.
      clear H0.
      destruct (i == idx); subst; eauto.
      replace s1 with s in * by ( eapply FMap.mapsto_unique; eauto ).
      econstructor; eauto 10.
      eapply IHclos_refl_trans_1n; eauto.
  Unshelve.
    all: eauto.
  Qed.

  Hint Resolve exec_any_slice.
  Hint Resolve exec_others_slice.


  Lemma horiz_left_movers :
    forall `(p : proc _ T) P,
      left_movers sliceStep P p ->
      forall i,
        left_movers (horizStep indexT sliceStep)
          (fun tid S => forall s, FMap.MapsTo i s S -> P tid s)
          (SliceProc i p).
  Proof.
    induction 1; simpl; intros; eauto.
    econstructor; intros.
    - eauto.
    - admit.
    - eapply left_movers_impl; eauto.
      simpl; intros; repeat deex.

      eapply exec_others_preserves_slice in H6 as H6'; eauto.
      repeat deex.
      eapply exec_any_preserves_slice in H5 as H5'; eauto.
      repeat deex.

      eauto 10.
  Admitted.


  Theorem horiz_ysa_movers :
    forall `(p : proc _ T),
      ysa_movers sliceStep p ->
      forall i,
        ysa_movers (horizStep indexT sliceStep) (SliceProc i p).
  Proof.
    unfold ysa_movers; intros.
    eapply right_movers_impl with
      (P1 := fun tid S => forall s, FMap.MapsTo i s S -> any tid s);
      [ | firstorder ].
    generalize dependent H.
    generalize (@any sliceState).
    intros.
    induction H.
    {
      simpl.
      econstructor; eauto; intros.
      eapply right_movers_impl; eauto.
      simpl; intros; repeat deex.

      eapply exec_others_preserves_slice in H5 as H5'; eauto.
      repeat deex.
      eapply exec_any_preserves_slice in H4 as H4'; eauto.
      repeat deex.

      eauto 10.
    }

    eapply RightMoversDone.
    inversion H; clear H; subst; repeat sigT_eq.
    {
      eapply ZeroNonMovers.
      eapply horiz_left_movers; eauto.
    }

    simpl.
    eapply OneNonMover.
    {
      intros.
      eapply left_movers_impl.
      eapply horiz_left_movers; eauto.
      simpl; intros; repeat deex.

      eapply exec_others_preserves_slice in H3 as H3'; eauto.
      repeat deex.
      eapply exec_any_preserves_slice in H1 as H1'; eauto.
      repeat deex.
      eauto 10.
    }

    eapply OneFinalNonMover.

  Unshelve.
    all: exact unit.
  Qed.

End HorizontalCompositionMovers.


(** Module structures for horizontal composition *)

Module Type HIndex.
  Axiom indexT : Type.
  Axiom indexValid : indexT -> Prop.
  Axiom indexCmp : Ordering indexT.
End HIndex.

Module HOps (o : Ops) (i : HIndex) <: Ops.
  Definition opT := horizOpT i.indexT o.opT.
End HOps.

Module HState (s : State) (i : HIndex) <: State.
  Definition State := @horizState i.indexT i.indexCmp s.State.
  Definition initP : State -> Prop :=
    horizInitP i.indexValid s.initP.
End HState.

Module HLayer (o : Ops) (s : State) (l : Layer o s) (i : HIndex).
  Definition step := @horizStep i.indexT i.indexCmp _ _ l.step.
End HLayer.

Module HProtocol (o : Ops) (s : State) (p : Protocol o s) (i : HIndex).
  Module ho := HOps o i.
  Module hs := HState s i.
  Definition step_allow T (hop : ho.opT T) (tid : nat) (S : hs.State) : Prop :=
    match hop with
    | Slice i op =>
      exists s,
        FMap.MapsTo i s S /\
        p.step_allow op tid s
    end.
End HProtocol.


Module LayerImplAbsHT
  (o : Ops)
  (s1 : State) (l1 : Layer o s1)
  (s2 : State) (l2 : Layer o s2)
  (a : LayerImplAbsT o s1 l1 s2 l2)
  (i : HIndex).

  Module ho := HOps o i.
  Module hs1 := HState s1 i.
  Module hs2 := HState s2 i.
  Module hl1 := HLayer o s1 l1 i.
  Module hl2 := HLayer o s2 l2 i.

  Definition absR :=
    @horizAbsR i.indexT i.indexCmp _ _ a.absR.

  Theorem absInitP :
    forall s1 s2,
      hs1.initP s1 ->
      absR s1 s2 ->
      hs2.initP s2.
  Proof.
    eapply horizAbsR_initP_ok.
    eapply a.absInitP.
  Qed.

  Theorem absR_ok :
    op_abs absR hl1.step hl2.step.
  Proof.
    eapply horizAbsR_ok.
    apply a.absR_ok.
  Qed.

End LayerImplAbsHT.


Module LayerImplMoversProtocolHT
  (s : State)
  (o1 : Ops) (l1raw : Layer o1 s) (l1 : Layer o1 s)
  (o2 : Ops) (l2 : Layer o2 s)
  (p : Protocol o1 s)
  (a : LayerImplMoversProtocolT s o1 l1raw l1 o2 l2 p)
  (i : HIndex).

  Module hs := HState s i.
  Module ho1 := HOps o1 i.
  Module ho2 := HOps o2 i.
  Module hl1raw := HLayer o1 s l1raw i.
  Module hl1 := HLayer o1 s l1 i.
  Module hl2 := HLayer o2 s l2 i.
  Module hp := HProtocol o1 s p i.

  Definition compile_op T (op : ho2.opT T) : proc ho1.opT T :=
    match op with
    | Slice i op => SliceProc i (a.compile_op op)
    end.

  Theorem compile_op_no_atomics : forall T (op : ho2.opT T),
    no_atomics (compile_op op).
  Proof.
    destruct op; simpl.
    pose proof (a.compile_op_no_atomics op).
    generalize dependent H.
    generalize (a.compile_op op).
    clear.
    induction 1; simpl; eauto.
  Qed.

  Theorem ysa_movers : forall T (op : ho2.opT T),
    ysa_movers hl1.step (compile_op op).
  Proof.
    destruct op; simpl.
    eapply horiz_ysa_movers.
    eapply a.ysa_movers.
  Qed.

  Lemma atomic_exec_horizStep : forall `(p : proc _ T) i tid S v S' evs,
    atomic_exec hl1.step (SliceProc i p) tid S v S' evs ->
      exists s s',
        FMap.MapsTo i s S /\
        S' = FMap.add i s' S /\
        atomic_exec l1.step p tid s v s' evs.
  Proof.
    (* NOT ACTUALLY TRUE: SLICE MIGHT NOT EXIST *)
  Admitted.

  Theorem compile_correct :
    compile_correct compile_op hl1.step hl2.step.
  Proof.
    intro; intros.
    destruct op; simpl in *.
    eapply atomic_exec_horizStep in H; repeat deex.
    eapply a.compile_correct in H1.
    econstructor; eauto.
  Qed.

  Theorem op_follows_protocol : forall tid s `(op : ho2.opT T),
    follows_protocol_proc hl1raw.step hp.step_allow tid s (compile_op op).
  Proof.
    destruct op; simpl.
    pose proof (a.op_follows_protocol).
  Admitted.

  Theorem allowed_stable :
    forall `(op : ho1.opT T) `(op' : ho1.opT T') tid tid' s s' r evs,
      tid <> tid' ->
      hp.step_allow op tid s ->
      hl1.step op' tid' s r s' evs ->
      hp.step_allow op tid s'.
  Proof.
    destruct op, op'.
    intros.
    inversion H0; clear H0; intuition idtac.
    inversion H1; clear H1; subst; repeat sigT_eq.
    pose (i.indexCmp).
    destruct (i == i0); subst.
    - replace s0 with x in * by ( eapply FMap.mapsto_unique; eauto ).
      econstructor; split.
      eapply FMap.add_mapsto.
      eapply a.allowed_stable; eauto.
    - econstructor; split.
      eapply FMap.mapsto_add_ne'; eauto.
      eauto.
  Qed.

  Theorem raw_step_ok :
    forall `(op : ho1.opT T) tid s r s' evs,
      restricted_step hl1raw.step hp.step_allow op tid s r s' evs ->
      hl1.step op tid s r s' evs.
  Proof.
    destruct op.
    unfold restricted_step; intuition idtac.
    inversion H0; clear H0; intuition idtac.
    inversion H1; clear H1; subst; repeat sigT_eq.
    eapply FMap.mapsto_unique in H0 as H0'; eauto; subst.
    econstructor; eauto.
    eapply a.raw_step_ok.
    constructor; eauto.
  Qed.

End LayerImplMoversProtocolHT.


Module LayerImplMoversHT
  (s : State)
  (o1 : Ops) (l1 : Layer o1 s)
  (o2 : Ops) (l2 : Layer o2 s)
  (a : LayerImplMoversT s o1 l1 o2 l2)
  (i : HIndex).

  Module hs := HState s i.
  Module ho1 := HOps o1 i.
  Module ho2 := HOps o2 i.
  Module hl1 := HLayer o1 s l1 i.
  Module hl2 := HLayer o2 s l2 i.

  Definition compile_op T (op : ho2.opT T) : proc ho1.opT T :=
    match op with
    | Slice i op => SliceProc i (a.compile_op op)
    end.

  Theorem compile_op_no_atomics : forall T (op : ho2.opT T),
    no_atomics (compile_op op).
  Proof.
    destruct op; simpl.
    pose proof (a.compile_op_no_atomics op).
    generalize dependent H.
    generalize (a.compile_op op).
    clear.
    induction 1; simpl; eauto.
  Qed.

  Theorem ysa_movers : forall T (op : ho2.opT T),
    ysa_movers hl1.step (compile_op op).
  Proof.
    destruct op; simpl.
    eapply horiz_ysa_movers.
    eapply a.ysa_movers.
  Qed.

  Lemma atomic_exec_horizStep : forall `(p : proc _ T) i tid S v S' evs,
    atomic_exec hl1.step (SliceProc i p) tid S v S' evs ->
      exists s s',
        FMap.MapsTo i s S /\
        S' = FMap.add i s' S /\
        atomic_exec l1.step p tid s v s' evs.
  Proof.
    (* NOT ACTUALLY TRUE: SLICE MIGHT NOT EXIST *)
  Admitted.

  Theorem compile_correct :
    compile_correct compile_op hl1.step hl2.step.
  Proof.
    intro; intros.
    destruct op; simpl in *.
    eapply atomic_exec_horizStep in H; repeat deex.
    eapply a.compile_correct in H1.
    econstructor; eauto.
  Qed.

End LayerImplMoversHT.


Module LayerImplLoopHT
  (s : State)
  (o1 : Ops) (l1 : Layer o1 s)
  (o2 : Ops) (l2 : Layer o2 s)
  (a : LayerImplLoopT s o1 l1 o2 l2)
  (i : HIndex).

  Module hs := HState s i.
  Module ho1 := HOps o1 i.
  Module ho2 := HOps o2 i.
  Module hl1 := HLayer o1 s l1 i.
  Module hl2 := HLayer o2 s l2 i.

  Definition compile_op T (op : ho2.opT T) :
    (option T -> ho1.opT T) * (T -> bool) * option T :=
    match op with
    | Slice idx op' =>
      let '(p, cond, i) := a.compile_op op' in
        ((fun x => Slice idx (p x)), cond, i)
    end.

  Theorem noop_or_success :
    noop_or_success compile_op hl1.step hl2.step.
  Proof.
    intro; intros.
    destruct opM; simpl in *.
    destruct (a.compile_op op) eqn:He.
    destruct p.
    inversion H; clear H; subst.
    inversion H0; clear H0; subst; repeat sigT_eq.
    edestruct a.noop_or_success; eauto.
    - left. intuition idtac.
      subst.
      admit.
    - right. intuition idtac.
      econstructor; eauto.
  Admitted.

End LayerImplLoopHT.
