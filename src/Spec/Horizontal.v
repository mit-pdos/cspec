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
    forall `(op : sliceOpT T) P ,
      left_mover_pred sliceStep op P ->
      forall i,
        left_mover_pred (horizStep indexT sliceStep) (Slice i op)
          (fun tid S => exists s, FMap.MapsTo i s S /\ P tid s).
  Proof.
    intros.
    split; intros.
    - eapply horiz_enabled_stable.
      destruct H; eauto.
    - inversion H0; clear H0; subst; repeat sigT_eq.
      eapply H in H10 as H'; intuition subst; deex.
      inversion H4; clear H4; subst; repeat sigT_eq.
      destruct (i == idx); subst.
      * replace s2 with s3 in * by ( eapply FMap.mapsto_unique; eauto ).
        eapply FMap.mapsto_add in H7; subst.
        eapply H1 in H13; eauto; deex.
        eexists; split.
        + econstructor; eauto.
        + rewrite FMap.add_add.
          erewrite <- FMap.add_add with (v1 := s').
          econstructor; eauto.
      * eapply FMap.mapsto_add_ne in H7; eauto.
        replace s2 with s in * by ( eapply FMap.mapsto_unique; eauto ).
        eexists; split.
        + econstructor; eauto.
        + rewrite FMap.add_add_ne by eauto.
          econstructor; eauto.
  Qed.

End HorizontalCompositionMovers.
