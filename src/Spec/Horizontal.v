Require Import ProofIrrelevance.
Require Import FunctionalExtensionality.
Require Import List.

Require Import ProofAutomation.
Require Import Ordering.
Require Import Helpers.ListStuff.
Require Import Helpers.Maps.
Require Import Helpers.Instances.
Require Import Spec.ConcurExec.
Require Import Spec.Equiv.
Require Import Spec.Patterns.
Require Import Spec.Abstraction.
Require Import Spec.Movers.
Require Import Spec.Compile.
Require Import Spec.CompileLoop.
Require Import Spec.Protocol.

Require Import Coq.Program.Equality.


Import ListNotations.

Global Set Implicit Arguments.
Global Generalizable All Variables.

Record HIndex :=
  { indexT :> Type;
    indexValid : indexT -> Prop;
    indexCmp : Ordering indexT; }.

Instance hindex_Ordering (x:HIndex) : Ordering x := indexCmp x.

Section HorizontalComposition.

  Variable ind : HIndex.

  Variable sliceOpT : Type -> Type.
  Variable sliceState : Type.
  Variable sliceStep : OpSemantics sliceOpT sliceState.
  Variable initP : sliceState -> Prop.

  Definition validIndexT := { i : ind.(indexT) | ind.(indexValid) i }.

  Inductive CheckResult :=
  | Missing
  | Present : validIndexT -> CheckResult
  .

  Inductive horizOpT : Type -> Type :=
  | Slice : forall (i : validIndexT) T (op : sliceOpT T), horizOpT T
  | CheckSlice : forall (i : ind.(indexT)), horizOpT CheckResult
  .

  Record horizState := mk_horizState {
    HSMap : FMap.t ind.(indexT) sliceState;
    HSValid : forall i, ind.(indexValid) i -> FMap.In i HSMap;
  }.

  Definition hget (S : horizState) (i : validIndexT) : sliceState.
    destruct S.
    destruct i.
    eapply HSValid0 in i.
    eapply FMap.in_mapsto_get in i.
    destruct i.
    exact x0.
  Defined.

  Definition hadd (i : validIndexT) (s : sliceState) (S : horizState) : horizState.
    destruct S.
    destruct i.
    refine (mk_horizState (FMap.add x s HSMap0) _).
    intros.
    eapply FMap.add_incr; eauto.
  Defined.

  Theorem hget_mapsto :
    forall i m,
      FMap.MapsTo (proj1_sig i) (hget m i) (HSMap m).
  Proof.
    destruct m.
    destruct i.
    simpl in *.
    destruct (FMap.in_mapsto_get x HSMap0 (HSValid0 x i)).
    eauto.
  Qed.

  Theorem hget_mapsto' :
    forall i m P,
      FMap.MapsTo i (hget m (exist _ i P)) (HSMap m).
  Proof.
    destruct m; simpl; intros.
    destruct (FMap.in_mapsto_get i HSMap0 (HSValid0 i P)).
    eauto.
  Qed.

  Opaque FMap.add.

  Theorem hget_hadd_eq : forall S s i H0 H1,
    hget (hadd (exist _ i H0) s S) (exist _ i H1) = s.
  Proof.
    destruct S; simpl; intros.
    match goal with
    | |- context[FMap.in_mapsto_get ?a ?b ?c] => destruct (FMap.in_mapsto_get a b c)
    end.
    eapply FMap.mapsto_add in m; eauto.
  Qed.

  Local Theorem hget_hadd_eq_general : forall i s s',
      hget (hadd i s s') i = s.
  Proof.
    destruct i; intros.
    apply hget_hadd_eq.
  Qed.

  Local Theorem hget_hadd_ne : forall S s i i' H0 H1,
    i <> i' ->
    hget (hadd (exist _ i H0) s S) (exist _ i' H1) = hget S (exist _ i' H1).
  Proof.
    destruct S; simpl; intros.
    repeat match goal with
    | |- context[FMap.in_mapsto_get ?a ?b ?c] => destruct (FMap.in_mapsto_get a b c)
    end.
    eapply FMap.mapsto_add_ne in m; eauto.
    FMap.mapsto_unique; auto.
  Qed.

  Local Theorem hget_hadd_ne_general : forall i i' s S,
      i <> i' ->
      hget (hadd i s S) i' = hget S i'.
  Proof.
    intros.
    destruct i, i'.
    destruct (x == x0); subst.
    exfalso.
    apply H.
    f_equal; auto using proof_irrelevance.
    apply hget_hadd_ne; auto.
  Qed.

  Theorem hadd_hget_eq : forall S i H0 H1,
    hadd (exist _ i H0) (hget S (exist _ i H1)) S = S.
  Proof.
    destruct S; simpl; intros.
    repeat match goal with
    | |- context[FMap.in_mapsto_get ?a ?b ?c] => destruct (FMap.in_mapsto_get a b c)
    end.
    match goal with
    | |- {| HSMap := ?m ; HSValid := ?v |} = _ =>
      generalize v; remember m
    end.
    rewrite FMap.mapsto_add_nilpotent in Heqt; eauto.
    subst; intros.
    f_equal.
    apply proof_irrelevance.
  Qed.

  Local Theorem hadd_hadd_eq : forall S s s' i H0 H1,
    hadd (exist _ i H0) s (hadd (exist _ i H1) s' S) = hadd (exist _ i H0) s S.
  Proof.
    destruct S; simpl; intros.
    match goal with
    | |- {| HSMap := ?m ; HSValid := ?v |} = _ =>
      generalize v; remember m
    end.
    rewrite FMap.add_add in Heqt.
    subst; intros.
    f_equal.
    apply proof_irrelevance.
  Qed.

  Local Theorem hadd_hadd_ne : forall S s s' i i' H0 H1,
    i <> i' ->
    hadd (exist _ i H0) s (hadd (exist _ i' H1) s' S) =
    hadd (exist _ i' H1) s' (hadd (exist _ i H0) s S).
  Proof.
    destruct S; simpl; intros.
    match goal with
    | |- {| HSMap := ?m ; HSValid := ?v |} = _ =>
      generalize v; remember m
    end.
    rewrite FMap.add_add_ne in Heqt; eauto.
    subst; intros.
    f_equal.
    apply proof_irrelevance.
  Qed.

  Inductive sameSlice : CheckResult -> ind.(indexT) -> Prop :=
  | SameSliceMissing : forall i,
    sameSlice Missing i
  | SameSlicePresent : forall i P,
    sameSlice (Present (exist _ i P)) i
  .

  Inductive horizStep :
      forall T, horizOpT T -> nat -> horizState -> T -> horizState -> list event -> Prop :=
  | StepSlice :
    forall tid idx (S : horizState) `(op : sliceOpT T) r s' evs,
      sliceStep op tid (hget S idx) r s' evs ->
      horizStep (Slice idx op) tid S r (hadd idx s' S) evs
  | StepCheckSlice :
    forall tid idx (S : horizState) r,
      sameSlice r idx ->
      horizStep (CheckSlice idx) tid S r S nil
  .

  Definition horizInitP (S : horizState) :=
    forall i,
      ind.(indexValid) i ->
      exists s,
        FMap.MapsTo i s (HSMap S) /\
        initP s.

  Definition SliceProc (i : validIndexT) `(p : proc sliceOpT T) : proc horizOpT T :=
    Compile.compile (fun T (op : sliceOpT T) => Call (Slice i op)) p.

  Theorem SliceProc_eq : forall i T (p p': proc _ T),
      SliceProc i p = SliceProc i p' ->
      p = p'.
  Proof.
    induction p; intros;
      try solve [ destruct p'; simpl in *; try congruence; invert H; auto ].
    - destruct p'; simpl in *; try congruence.
      invert H0; eauto.
      f_equal; eauto.
      extensionality r.
      invert H0.
      apply equal_f with r in H5.
      eauto.
    - destruct p'; simpl in *; try congruence.
      invert H0.
      f_equal.
      extensionality x.
      apply equal_f with x in H3.
      eauto.
    - destruct p'; simpl in *; try congruence.
      invert H.
      f_equal.
      eauto.
    - dependent destruction p'; simpl in *; try congruence.
      invert H.
      erewrite IHp; eauto.
  Qed.

End HorizontalComposition.

Arguments horizState ind sliceState.
Arguments horizStep ind {sliceOpT sliceState} sliceStep.
Arguments Slice {ind sliceOpT} i {T}.
Arguments CheckSlice {ind sliceOpT} i.
Arguments Missing {ind}.

Ltac destruct_horizState :=
  match goal with
  | x : horizState _ _ |- _ => destruct x; simpl in *
  end.

Ltac destruct_validIndex :=
  match goal with
  | x : validIndexT _ |- _ => destruct x; simpl in *
  end.

Ltac destruct_ind :=
  match goal with
  | x : indexT _ _ |- _ => unfold indexT in x; simpl in *
  | x : indexValid _ _ |- _ => unfold indexValid in x; simpl in *
  end.

Section HorizontalCompositionAbs.

  Variable ind : HIndex.

  Variable sliceOpT : Type -> Type.

  Variable sliceState1 : Type.
  Variable sliceStep1 : OpSemantics sliceOpT sliceState1.

  Variable sliceState2 : Type.
  Variable sliceStep2 : OpSemantics sliceOpT sliceState2.

  Variable absR : sliceState1 -> sliceState2 -> Prop.

  Definition horizAbsR (S1 : horizState ind sliceState1)
                       (S2 : horizState ind sliceState2) : Prop :=
    forall (i : ind.(indexT)),
      ind.(indexValid) i ->
      ( forall s1,
          FMap.MapsTo i s1 (HSMap S1) ->
            exists s2, FMap.MapsTo i s2 (HSMap S2) /\ absR s1 s2 ) /\
      ( forall s2,
          FMap.MapsTo i s2 (HSMap S2) ->
            exists s1, FMap.MapsTo i s1 (HSMap S1) /\ absR s1 s2 ).

  Hint Resolve FMap.add_mapsto.
  Hint Resolve FMap.mapsto_add_ne'.
  Hint Resolve FMap.mapsto_in.

  Theorem horizAbsR_ok :
    op_abs absR sliceStep1 sliceStep2 ->
    op_abs horizAbsR (horizStep ind sliceStep1) (horizStep ind sliceStep2).
  Proof.
    unfold op_abs, horizAbsR; intros.
    inversion H1; clear H1; subst; repeat sigT_eq.
    {
      eapply H in H7; repeat deex.
      {
        eexists; split; [ | econstructor; eauto ].
        intros.
        repeat destruct_horizState.
        repeat destruct_validIndex.
        destruct (i == x); subst.
        - split; intros.
          + eapply FMap.mapsto_add_eq in H4; subst; eauto.
          + eapply FMap.mapsto_add_eq in H4; subst; eauto.
        - specialize (H0 i); intuition idtac.
          + eapply FMap.mapsto_add_ne in H4; eauto.
            specialize (H0 _ H4); propositional; eauto.
          + eapply FMap.mapsto_add_ne in H4; eauto.
            specialize (H5 _ H4); propositional; eauto.
      }
      {
        pose proof (@hget_mapsto _ _ idx s1).
        pose proof (@hget_mapsto _ _ idx s2).
        specialize (H0 (proj1_sig idx) (proj2_sig idx)).
        eapply H0 in H1; deex.
        FMap.mapsto_unique; eauto.
      }
    }
    {
      eexists.
      split.
      eassumption.
      constructor.
      intuition idtac.
    }
  Qed.

  Variable initP1 : sliceState1 -> Prop.
  Variable initP2 : sliceState2 -> Prop.

  (* this is like the normal absInitP but strengthens it to provide an explicit
  function for the witness - this is needed to construct the horizontal abstract
  state *)
  Variable initP_map : sliceState1 -> sliceState2.
  Variable initP_ok :
    forall s1,
      initP1 s1 ->
      absR s1 (initP_map s1) /\
      initP2 (initP_map s1).

  Hint Resolve FMap.mapsto_in.
  Hint Resolve FMap.map_values_MapsTo.

  Theorem horizAbsR_initP_ok :
    forall s1,
      horizInitP initP1 s1 ->
      exists s2, horizAbsR s1 s2 /\
            horizInitP initP2 s2.
  Proof.
    unfold horizInitP; intros.

    unshelve eexists {| HSMap := FMap.map_values initP_map s1.(HSMap) |};
      simpl;
      intuition idtac.
    - intros.
      specialize (H i); propositional.
      rewrite <- FMap.map_values_in; eauto.
    - unfold horizAbsR; simpl; intros.
      specialize (H _ H0); propositional.
      eapply initP_ok in H1; propositional.
      split; intros.
      + FMap.mapsto_unique; eauto.
      + eapply FMap.map_values_MapsTo_general in H3; propositional.
        FMap.mapsto_unique; eauto.
    - specialize (H i); propositional.
      apply initP_ok in H1; propositional.
      eauto.
  Qed.

End HorizontalCompositionAbs.

Print horizAbsR.
Arguments horizAbsR ind {sliceState1 sliceState2} absR.

Section HorizontalCompositionMovers.

  Variable ind : HIndex.

  Variable sliceOpT : Type -> Type.
  Variable sliceState : Type.
  Variable sliceStep : OpSemantics sliceOpT sliceState.

  Hint Resolve FMap.add_mapsto.
  Hint Resolve FMap.mapsto_add_ne'.
  Hint Resolve FMap.mapsto_in.
  Hint Resolve FMap.add_in_in.
  Hint Resolve FMap.add_incr.
  Hint Constructors horizStep.
  Hint Extern 1 (horizStep _ _ _ _ _ _ _ _ _) => econstructor.

  Opaque hget.
  Opaque hadd.

  Local Theorem horiz_right_mover_ok :
    forall `(op : sliceOpT T),
      right_mover sliceStep op ->
      forall i,
        right_mover (horizStep ind sliceStep) (Slice i op).
  Proof.
    intros.
    unfold right_mover; intros.
    inversion H0; clear H0; subst; repeat sigT_eq.
    eapply H in H9 as H'; intuition subst.
    inversion H3; clear H3; subst; repeat sigT_eq.
    {
      repeat destruct_horizState.
      repeat destruct_validIndex.
      destruct (x == x0); subst.
      - rewrite hget_hadd_eq in *.
        eapply H1 in H8; eauto; deex.
        eexists; split.
        + econstructor; eauto.
          replace i0 with i by apply proof_irrelevance; eauto.
        + rewrite hadd_hadd_eq.
          erewrite <- hadd_hadd_eq with (s := s'0).
          replace i0 with i by apply proof_irrelevance; eauto.
          econstructor; eauto.
          rewrite hget_hadd_eq; eauto.
      - rewrite hget_hadd_ne in * by eauto.
        eexists; split.
        + econstructor; eauto.
        + rewrite hadd_hadd_ne by eauto.
          econstructor; eauto.
          rewrite hget_hadd_ne by eauto.
          eauto.
    }
    {
      eexists; split; eauto.
    }
  Qed.

  Theorem horiz_enabled_stable :
    forall `(op : sliceOpT T),
      enabled_stable sliceStep T op ->
      forall i,
        enabled_stable (horizStep ind sliceStep) T (Slice i op).
  Proof.
    intros.
    unfold enabled_stable; intros.
    unfold enabled_in in *; repeat deex.
    inversion H1; clear H1; subst; repeat sigT_eq.
    inversion H2; clear H2; subst; repeat sigT_eq; eauto.
    repeat destruct_validIndex.
    destruct (x == x0); subst.
    - edestruct H.
      eassumption.
      unfold enabled_in; eauto.
      replace i0 with i in * by apply proof_irrelevance; eauto.
      repeat deex.
      do 3 eexists. econstructor; eauto.
      rewrite hget_hadd_eq; eauto.
    - do 3 eexists. econstructor; eauto.
      rewrite hget_hadd_ne; eauto.
  Qed.

  Local Theorem horiz_left_mover_ok :
    forall `(op : sliceOpT T),
      left_mover sliceStep op ->
      forall i,
        left_mover (horizStep ind sliceStep) (Slice i op).
  Proof.
    intros.
    split; intros.
    - eapply horiz_enabled_stable.
      destruct H; eauto.
    - inversion H0; clear H0; subst; repeat sigT_eq.
      eapply H in H9 as H'; intuition subst.
      inversion H3; clear H3; subst; repeat sigT_eq.
      {
        repeat destruct_validIndex.
        destruct (x == x0); subst.
        * rewrite hget_hadd_eq in *.
          replace i0 with i in * by apply proof_irrelevance; eauto.
          eapply H1 in H8; eauto; deex.
          eexists; split.
          + econstructor; eauto.
          + rewrite hadd_hadd_eq.
            erewrite <- hadd_hadd_eq with (s := s').
            econstructor; eauto.
            rewrite hget_hadd_eq; eauto.
        * rewrite hget_hadd_ne in * by eauto.
          eexists; split.
          + econstructor; eauto.
          + rewrite hadd_hadd_ne by eauto.
            econstructor; eauto.
            rewrite hget_hadd_ne by eauto.
            eauto.
      }
      {
        eexists; split; eauto.
      }
  Qed.

  Local Theorem horiz_left_mover_pred_ok :
    forall `(op : sliceOpT T) P,
      left_mover_pred sliceStep op P ->
      forall i,
        left_mover_pred (horizStep ind sliceStep) (Slice i op)
          (fun tid S => P tid (hget S i)).
  Proof.
    intros.
    split; intros.
    - eapply horiz_enabled_stable.
      destruct H; eauto.
    - inversion H0; clear H0; subst; repeat sigT_eq.
      eapply H in H9 as H'; intuition subst.
      inversion H4; clear H4; subst; repeat sigT_eq.
      {
        repeat destruct_validIndex.
        destruct (x == x0); subst.
        * rewrite hget_hadd_eq in *.
          replace i0 with i in * by apply proof_irrelevance; eauto.
          eapply H1 in H10; eauto; deex.
          eexists; split.
          + econstructor; eauto.
          + rewrite hadd_hadd_eq.
            erewrite <- hadd_hadd_eq with (s := s').
            econstructor; eauto.
            rewrite hget_hadd_eq; eauto.
        * rewrite hget_hadd_ne in * by eauto.
          eexists; split.
          + econstructor; eauto.
          + rewrite hadd_hadd_ne by eauto.
            econstructor; eauto.
            rewrite hget_hadd_ne by eauto.
            eauto.
      }
      {
        eexists; split; eauto.
      }
  Qed.

  Hint Resolve horiz_right_mover_ok.
  Hint Resolve horiz_left_mover_ok.
  Hint Resolve horiz_left_mover_pred_ok.


  Lemma atomic_exec_horizStep : forall `(p0 : proc _ T) i tid S v S' evs,
    atomic_exec (horizStep ind sliceStep) p0 tid S v S' evs ->
      forall p,
        p0 = SliceProc i p ->
        exists s',
          atomic_exec sliceStep p tid (hget S i) v s' evs /\
          S' = hadd i s' S.
  Proof.
    induction 1; simpl; intros.
    - destruct p; simpl in *; try congruence.
      inversion H; clear H; subst; repeat sigT_eq.
      eexists; split; eauto.
      destruct_validIndex.
      rewrite hadd_hget_eq; eauto.
    - destruct p; simpl in *; try congruence.
      inversion H1; clear H1; subst; repeat sigT_eq.
      edestruct IHatomic_exec1; eauto.
      edestruct IHatomic_exec2; eauto.
      intuition subst.
      destruct_validIndex.
      rewrite hget_hadd_eq in *.
      eexists; split; eauto.
      rewrite hadd_hadd_eq; eauto.
    - destruct p; simpl in *; try congruence.
      inversion H0; clear H0; subst; repeat sigT_eq.
      inversion H; clear H; subst; repeat sigT_eq.
      eauto.
    - destruct p0; simpl in *; try congruence.
      inversion H0; clear H0; subst; repeat sigT_eq.
      edestruct IHatomic_exec.
      + unfold until1.
        instantiate (1 := Bind (p0 v0) (fun x => if (c0 x) then Ret x else Until c0 (fun x0 => p0 x0) (Some x))).
        simpl; f_equal.
        eapply functional_extensionality; intros.
        destruct (c0 x); reflexivity.
      + intuition subst.
        eexists; split; eauto.
  Qed.

  Local Lemma hadd_hget_eq' : forall (i: validIndexT ind) (s: horizState _ sliceState),
      s = hadd i (hget s i) s.
  Proof.
    intros.
    destruct_validIndex.
    rewrite hadd_hget_eq; auto.
  Qed.

  Hint Resolve hadd_hget_eq'.

  Local Lemma exec_tid_slice :
    forall S1 S2 tid `(p : proc _ T) r spawned evs,
      exec_tid (horizStep ind sliceStep) tid S1 p S2 r spawned evs ->
      forall `(p' : proc _ T) i,
        p = SliceProc i p' ->
        exists spawned' s' r',
        spawned = match spawned' with
                  | Proc p => Proc (SliceProc i p)
                  | NoProc => NoProc
                  end /\
          exec_tid sliceStep tid (hget S1 i) p' s' r' spawned' evs /\
          S2 = hadd i s' S1 /\
          match r with
          | inl v => r' = inl v
          | inr rx => exists rx', r' = inr rx' /\ rx = SliceProc i rx'
          end.
  Proof.
    induction 1; intros; subst.
    - exists NoProc; simpl.
      destruct p'; simpl in *; try congruence.
      invert H.
      descend; simpl; intuition eauto.
    - exists NoProc; simpl.
      destruct p'; simpl in *; try congruence.
      invert H0.
      invert H.
      eauto 10.
    - exists NoProc; simpl.
      destruct p'; simpl in *; try congruence.
      inversion H0; clear H0; subst; repeat sigT_eq.
      eapply atomic_exec_horizStep in H; eauto; deex.
      eauto 10.
    - destruct p'; simpl in *; try congruence.
      inversion H0; clear H0; subst; repeat sigT_eq.
      edestruct IHexec_tid; eauto; repeat deex.
      descend; intuition eauto.
      destruct result; subst; eauto.
      deex; eauto.
    - exists NoProc; simpl.
      destruct p'; simpl in *; try congruence.
      invert H.
      descend; intuition eauto.
      descend; intuition eauto.
      unfold until1; simpl.
      f_equal.
      extensionality x.
      destruct matches.
    - dependent destruction p'; simpl in *; try congruence.
      invert H.
      eexists (Proc _).
      descend; intuition eauto.
  Qed.

  Local Lemma exec_any_slice :
    forall S1 S2 tid `(p : proc _ T) r,
      exec_any (horizStep ind sliceStep) tid S1 p r S2 ->
      forall `(p' : proc _ T) i,
        p = SliceProc i p' ->
        exec_any sliceStep tid (hget S1 i) p' r (hget S2 i).
  Proof.
    induction 1; intros; subst.
    - inversion H0; clear H0; subst; repeat sigT_eq; eauto.
      repeat destruct_validIndex.
      destruct (x == x0); subst; eauto.
      + replace i0 with i in * by apply proof_irrelevance.
        eapply ExecAnyOther.
        eassumption.
        2: eauto.
        rewrite hget_hadd_eq in *.
        eauto.
      + specialize (IHexec_any _ _ eq_refl).
        rewrite hget_hadd_ne in * by eauto.
        eauto.
    - eapply exec_tid_slice in H; eauto; repeat deex.
      destruct_validIndex.
      rewrite hget_hadd_eq; eauto.
    - eapply exec_tid_slice in H; eauto; repeat deex.
      eapply ExecAnyThisMore; eauto.
      specialize (IHexec_any _ _ eq_refl).
      destruct_validIndex.
      rewrite hget_hadd_eq in *.
      eapply IHexec_any.
  Qed.

  Local Lemma exec_others_slice :
    forall S1 S2 tid,
      exec_others (horizStep ind sliceStep) tid S1 S2 ->
      forall i,
        exec_others sliceStep tid (hget S1 i) (hget S2 i).
  Proof.
    induction 1; intros; eauto.
    repeat deex.
    inversion H1; clear H1; subst; repeat sigT_eq; eauto.
    repeat destruct_validIndex.
    destruct (x0 == x1); subst; eauto.
    * replace i0 with i in * by apply proof_irrelevance.
      econstructor; [ | apply IHclos_refl_trans_1n ].
      do 5 eexists; split; eauto.
      rewrite hget_hadd_eq; eauto.
    * specialize (IHclos_refl_trans_1n (exist _ x0 i)).
      rewrite hget_hadd_ne in * by eauto.
      eauto.
  Unshelve.
    all: try exact (Ret tt).
  Qed.

  Hint Resolve exec_any_slice.
  Hint Resolve exec_others_slice.

  Local Lemma horiz_left_movers :
    forall `(p : proc _ T) P,
      left_movers sliceStep P p ->
      forall i,
        left_movers (horizStep ind sliceStep)
          (fun tid S => P tid (hget S i))
          (SliceProc i p).
  Proof.
    induction 1; simpl; intros; eauto.
    econstructor; intros.
    - eauto.
    - eapply H0 in H3.
      edestruct H3; repeat deex.
      do 3 eexists.
      constructor.
      eauto.
    - eapply left_movers_impl; eauto.
      simpl; intros; repeat deex.

      do 2 eexists.
      intuition eauto.
  Qed.


  Local Theorem horiz_ysa_movers :
    forall `(p : proc _ T),
      ysa_movers sliceStep p ->
      forall i,
        ysa_movers (horizStep ind sliceStep) (SliceProc i p).
  Proof.
    unfold ysa_movers; intros.
    eapply right_movers_impl with
      (P1 := fun tid S => any tid (hget S i));
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

      do 2 eexists.
      intuition eauto.
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

      do 2 eexists.
      intuition eauto.
    }

    eapply OneFinalNonMover.
  Qed.

End HorizontalCompositionMovers.


(** Module structures for horizontal composition *)

Definition HOps (o: Type -> Type) (i: HIndex) :=
  horizOpT i o.

Definition HState (s: Type) (i: HIndex) :=
  @horizState i s.

Module HLayer.
  Import Layer.
  Section S.
    Context O
            S
            (l: Layer.t O S)
            (i: HIndex).

    Definition hstep := @horizStep i _ _ l.(step).
    Definition hinitP : @horizState i S -> Prop :=
      horizInitP l.(initP).
    Definition t : Layer.t (horizOpT i O) (horizState i S) :=
      {| step := hstep;
         initP := hinitP; |}.
  End S.
End HLayer.

Module HProtocol.
  Section S.
    Context O
            S
            (i : HIndex)
            (p : Protocol.t O S).
  Definition ho := horizOpT i O.
  Definition hs := horizState i S.
  Definition step_allow T (hop : ho T) (tid : nat) (S : hs) : Prop :=
    match hop with
    | Slice i op =>
      p.(Protocol.step_allow) _ op tid (hget S i)
    | CheckSlice i =>
      True
    end.
  Definition t : Protocol.t (horizOpT i O) (horizState i S) :=
    {| Protocol.step_allow := step_allow; |}.
  End S.
End HProtocol.

Check HProtocol.t.

Module HLayerImpl.
  Import Layer.
  Section S.
  Context O 
          S1
          S2
          `(l1: Layer.t O S1)
          `(l2: Layer.t O S2).
  Record t :=
  { absR : S1 -> S2 -> Prop;
    absR_ok : op_abs absR l1.(step) l2.(step);
    initP_map: forall (s1: S1), {s2: S2 | l1.(initP) s1 -> absR s1 s2 /\ l2.(initP) s2}; }.
  End S.
End HLayerImpl.

Module HLayerImplAbsT.
  Import Layer.
  Import HLayerImpl.
  Section S.
    Context O
            S1
            S2
            `(l1: Layer.t O S1)
            `(l2: Layer.t O S2)
            (a : HLayerImpl.t l1 l2).

  Theorem absInitP : forall s1,
      l1.(initP) s1 ->
      exists s2, a.(absR) s1 s2 /\
            l2.(initP) s2.
  Proof.
    intros.
    destruct (a.(initP_map) s1); eauto.
  Qed.

  Definition t : LayerImplAbsT.t l1 l2 :=
    {| LayerImplAbsT.absR := a.(absR);
       LayerImplAbsT.absR_ok := a.(absR_ok);
       LayerImplAbsT.absInitP := absInitP; |}.
  End S.
End HLayerImplAbsT.

Module HLayerImplAbs.
  Section S.
    Context O S1 S2
            (l1: Layer.t O S1)
            (l2: Layer.t O S2)
            (a : HLayerImpl.t l1 l2).

    Definition t : LayerImpl.t l1 l2 :=
      LayerImplAbs.t (HLayerImplAbsT.t a).
    End S.
End HLayerImplAbs.

Module LayerImplAbsHT.
  Import Layer.
  Import HLayerImpl.
  Import HLayerImplAbsT.
  Section S.
    Context O S1 S2
            `(l1: Layer.t O S1)
            `(l2: Layer.t O S2)
            (a : HLayerImpl.t l1 l2)
            (i : HIndex).

  Definition ho := HOps O i.
  Definition hs1 := HState S1 i.
  Definition hs2 := HState S2 i.
  Definition hl1 := HLayer.t l1 i.
  Definition hl2 := HLayer.t l2 i.

  Definition hliat := HLayerImplAbsT.t a.
  Definition hlia := HLayerImplAbs.t a.

  Definition absR :=
    @horizAbsR i _ _ a.(absR).

  Theorem absInitP :
    forall s1,
      hl1.(initP) s1 ->
      exists s2, absR s1 s2 /\
      hl2.(initP) s2.
  Proof.
    intros.
    eapply horizAbsR_initP_ok
      with (initP_map := fun s1 => proj1_sig (a.(initP_map) s1)) in H;
      propositional; eauto.
    pose proof hlia.
    exists s2.
    destruct X.
    split.
    unfold absR.
    destruct a.
    apply H.
    apply H0.
    pose proof (proj2_sig (a.(initP_map) s0));
      simpl in *; propositional; eauto.
    Qed.

  Theorem absR_ok :
    op_abs absR hl1.(step) hl2.(step).
  Proof.
    eapply horizAbsR_ok.
    apply a.(absR_ok).
  Qed.

  Definition t : LayerImplAbsT.t hl1 hl2.
    refine {| LayerImplAbsT.absR := absR;
              LayerImplAbsT.absInitP := absInitP;
              LayerImplAbsT.absR_ok := absR_ok; |}.
  Qed.

  End S.
End LayerImplAbsHT.

Module LayerImplMoversHT.
  Import LayerImplMoversT.
  Import Layer.
  Section S.
    Context
      S
      `(l1 : Layer.t O1 S)
      `(l2 : Layer.t O2 S)
      (a : LayerImplMoversT.t l1 l2)
      (i : HIndex).

  Definition hs := HState S i.
  Definition ho1 := HOps O1 i.
  Definition ho2 := HOps O2 i.
  Definition hl1 := HLayer.t l1 i.
  Definition hl2 := HLayer.t l2 i.

  Definition compile_op T (op : ho2 T) : proc ho1 T :=
    match op with
    | Slice i op => SliceProc i (a.(compile_op) op)
    | CheckSlice i => Call (CheckSlice i)
    end.

  Theorem compile_op_no_atomics : forall T (op : ho2 T),
    no_atomics (compile_op op).
  Proof.
    destruct op; simpl; eauto.
    pose proof (a.(compile_op_no_atomics) T op).
    generalize dependent H.
    generalize (a.(LayerImplMoversT.compile_op) op).
    clear.
    induction 1; simpl; eauto.
  Qed.

  Theorem ysa_movers : forall T (op : ho2 T),
      Movers.ysa_movers hl1.(Layer.step) (compile_op op).
  Proof.
    destruct op; simpl; eauto.
    eapply horiz_ysa_movers.
    eapply a.(ysa_movers).
  Qed.

  Check compile_correct.

  Theorem compile_correct :
    Compile.compile_correct compile_op hl1.(Layer.step) hl2.(Layer.step).
  Proof.
    intro; intros.
    destruct op; simpl in *.
    - eapply atomic_exec_horizStep in H; eauto; deex.
      eapply a.(compile_correct) in H.
      econstructor; eauto.
    - repeat atomic_exec_inv.
      inversion H5; clear H5; subst; repeat sigT_eq.
      econstructor; eauto.
  Qed.

  Theorem initP_compat :
    forall s, hl1.(Layer.initP) s -> hl2.(Layer.initP) s.
  Proof.
    unfold hl1, hl2, initP.
    unfold horizInitP; intros.
    unfold HLayer.t.
    unfold HLayer.t in H.
    unfold HLayer.hinitP.
    unfold HLayer.hinitP in H.
    unfold horizInitP in H.
    unfold horizInitP.
    pose proof a.(initP_compat) as initP.
    intros.
    specialize (H i0); propositional.
    eauto.
  Qed.
  End S.
End LayerImplMoversHT.

Module LayerImplMoversProtocolHT.
  Import LayerImplMoversProtocolT.
  Import LayerImplMoversT.
  Import HLayerImpl.
  Import HLayer.
  Import Layer.
  
  Section S.
    Context S O1 O2
            `(l1raw: Layer.t O1 S)
            `(l1: Layer.t O1 S)
            `(l2: Layer.t O2 S)
            (p : Protocol.t O1 S)
            (a : LayerImplMoversProtocolT.t l1raw l1 l2 p)
            (i : HIndex).

  Definition hs := HState S i.
  Definition ho1 := HOps O1 i.
  Definition ho2 := HOps O2 i.
  Definition hl1raw := HLayer.t l1raw i.
  Definition hl1 := HLayer.t l1 i.
  Definition hl2 := HLayer.t l2 i.
  Definition hp := HProtocol.t i p.
  Definition layerImplMoversT := a.(movers_impl).

  Definition compile_op T (op : ho2 T) : proc ho1 T :=
    match op with
    | Slice i op => SliceProc i (a.(compile_op) op)
    | CheckSlice i => Call (CheckSlice i)
    end.

  Theorem compile_op_no_atomics : forall T (op : ho2 T),
    no_atomics (compile_op op).
  Proof.
    destruct op; simpl; eauto.
    pose proof (a.(compile_op_no_atomics) T op).
    generalize dependent H.
    generalize (a.(LayerImplMoversT.compile_op) op).
    clear.
    induction 1; simpl; eauto.
  Qed.

  Theorem ysa_movers : forall T (op : ho2 T),
      Movers.ysa_movers hl1.(Layer.step) (compile_op op).
  Proof.
    destruct op; simpl; eauto.
    eapply horiz_ysa_movers.
    eapply a.(ysa_movers).
  Qed.

  Theorem compile_correct :
    Compile.compile_correct compile_op hl1.(step) hl2.(step).
  Proof.
    intro; intros.
    destruct op; simpl in *.
    - eapply atomic_exec_horizStep in H; eauto; deex.
      eapply a.(compile_correct) in H.
      econstructor; eauto.
    - repeat atomic_exec_inv.
      inversion H5; clear H5; subst; repeat sigT_eq.
      econstructor; eauto.
  Qed.

  Definition cmp := i.(indexCmp).
  Existing Instance cmp.

  Hint Rewrite hget_hadd_eq_general : h.
  Hint Rewrite hget_hadd_ne_general using solve [ auto ] : h.

  Lemma step_high_to_step_low :
    forall s s' (i: validIndexT i) T (op: ho1 T) tid r evs,
      restricted_step hl1raw.(step) hp.(Protocol.step_allow) op tid s r s' evs ->
      (exists (op': O1 T) r' evs',
          restricted_step l1raw.(step) p.(Protocol.step_allow) op' tid (hget s i) r' (hget s' i) evs') \/
      hget s i = hget s' i.
  Proof.
    intros.
    unfold restricted_step in *; propositional.
    unfold hp, hl1raw, Protocol.step_allow, Layer.step, HProtocol.t, HLayer.t in *.
    invert H0; clear H0.
    - destruct (i0 == idx); subst;
        autorewrite with h;
        eauto 10.
    - eauto.
  Qed.

  Lemma exec_ops_high : forall s s' (i: validIndexT i),
      exec_ops (restricted_step hl1raw.(step) hp.(Protocol.step_allow)) s s' ->
      exec_ops (restricted_step l1raw.(step) p.(Protocol.step_allow)) (hget s i) (hget s' i).
  Proof.
    unfold exec_ops; intros.
    induction H; propositional.
    reflexivity.

    transitivity (hget y i0); auto.
    eapply step_high_to_step_low with (i0:=i0) in H;
      (intuition propositional);
      eauto.
    - econstructor; [ | reflexivity ].
      descend; eauto.
    - replace (hget y i0).
      reflexivity.
  Qed.

  Theorem op_follows_protocol : forall tid s `(op : ho2 T),
    follows_protocol_proc hl1raw.(step) hp.(Protocol.step_allow) tid s (compile_op op).
  Proof.
    destruct op; simpl.
    - pose proof (a.(op_follows_protocol) tid (hget s i0) T op).
      generalize dependent (a.(LayerImplMoversT.compile_op) op); intros.
      clear dependent op.
      remember (hget s i0).
      generalize dependent s.
      generalize dependent i0.
      induction H; intros; subst; simpl.
      + constructor. eauto.
      + constructor. eauto.
        intros.
        eapply H1; eauto.
        eapply exec_any_slice; eauto.
        eapply exec_any_impl; try eassumption.

        clear.
        unfold restricted_step; intuition idtac.
        inversion H1; clear H1; subst; repeat sigT_eq; simpl in *.
        * econstructor; eauto.
        * econstructor; eauto.
      + constructor; intros.
        eapply H0; eauto.
      + constructor.
      + constructor; intros.
        assert (forall tid', tid <> tid' ->
                        follows_protocol_proc hl1raw.(step) hp.(Protocol.step_allow)
                                              tid' s0 (SliceProc i0 p0)).
        eauto.
        rename H into Hspawn.
        unfold spawn_follows_protocol; intros.
        specialize (H1 tid' ltac:(auto)).
        specialize (H0 tid' ltac:(auto)).
        specialize (Hspawn tid' ltac:(auto)).

        assert (exec_ops (restricted_step l1raw.(step) p.(Protocol.step_allow))
                         (hget s0 i0) (hget s' i0)).
        eapply exec_ops_high; eauto.
        eauto.
    - constructor; constructor.
  Qed.

  Theorem allowed_stable :
    forall `(op : ho1 T) `(op' : ho1 T') tid tid' s s' r evs,
      tid <> tid' ->
      hp.(Protocol.step_allow) T op tid s ->
      hl1.(step) op' tid' s r s' evs ->
      hp.(Protocol.step_allow) T op tid s'.
  Proof.
    destruct op, op'; eauto.
    {
      intros.
      simpl in *.
      inversion H1; clear H1; subst; repeat sigT_eq.
      pose (i.(indexCmp)).
      repeat destruct_validIndex.
      destruct (x == x0); subst.
      - replace i1 with i0 in * by apply proof_irrelevance.
        rewrite hget_hadd_eq.
        eapply a.(allowed_stable); eauto.
      - rewrite hget_hadd_ne in * by eauto.
        eauto.
    }
    {
      intros.
      inversion H1; subst; eauto.
    }
  Qed.

  Theorem raw_step_ok :
    forall `(op : ho1 T) tid s r s' evs,
      restricted_step hl1raw.(step) hp.(Protocol.step_allow) op tid s r s' evs ->
      hl1.(step) op tid s r s' evs.
  Proof.
    destruct op.
    - unfold restricted_step; intuition idtac.
      inversion H1; clear H1; subst; repeat sigT_eq.
      econstructor; eauto.
      eapply a.(raw_step_ok).
      constructor; eauto.
    - unfold restricted_step; intuition idtac.
      inversion H1; clear H1; subst; repeat sigT_eq.
      econstructor; eauto.
  Qed.

  Theorem initP_compat : forall s, hl1.(initP) s -> hl2.(initP) s.
  Proof.
    unfold hl1, hl2, initP, horizInitP, HLayer.t, hinitP, horizInitP; intros.
    pose proof a.(initP_compat).
    specialize (H i0); propositional.
    eauto.
  Qed.

  Theorem raw_initP_compat : forall s, hl1raw.(initP) s -> hl1.(initP) s.
  Proof.
    unfold hl1raw, hl1, initP, horizInitP, HLayer.t, hinitP, horizInitP; intros.
    pose proof a.(raw_initP_compat).
    specialize (H i0); propositional.
    eauto.
  Qed.
  End S.
End LayerImplMoversProtocolHT.

Module LayerImplLoopHT.
  Import LayerImplLoopT.
  Import Layer.
  Section S.
  Context S
          `(l1 : Layer.t O1 S)
          `(l2 : Layer.t O2 S)
          (a : LayerImplLoopT.t l1 l2)
          (i : HIndex).

  Definition hs := HState S i.
  Definition ho1 := HOps O1 i.
  Definition ho2 := HOps O2 i.
  Definition hl1 := HLayer.t l1 i.
  Definition hl2 := HLayer.t l2 i.

  Definition compile_op T (op : ho2 T) :
    (option T -> ho1 T) * (T -> bool) * option T :=
    match op with
    | @Slice _ _ idx T' op' =>
      let '(p, cond, i0) := LayerImplLoopT.compile_op a T' op' in
      (fun x => Slice idx (p x), cond, i0)
    | CheckSlice idx =>
      ((fun _ => CheckSlice idx),
       fun _ => true,
             None)
    end.

  Theorem noop_or_success :
    CompileLoop.noop_or_success compile_op hl1.(step) hl2.(step).
  Proof.
    intro; intros.
    destruct opM; simpl in *.
    {
      destruct (a.(LayerImplLoopT.compile_op) T op) eqn:He.
      destruct p.
      inversion H; clear H; subst.
      inversion H0; clear H0; subst; repeat sigT_eq.
      edestruct a.(noop_or_success); [ now eauto | now eauto | .. ].
      - left. intuition idtac.
        subst.
        destruct_validIndex.
        rewrite hadd_hget_eq; eauto.
      - right. intuition idtac.
        econstructor; eauto.
    }
    {
      inversion H; clear H; subst.
      inversion H0; clear H0; subst; repeat sigT_eq.
      right; intuition eauto.
      econstructor; eauto.
    }
  Qed.

  Theorem initP_compat :
    forall s, hl1.(initP) s -> hl2.(initP) s.
  Proof.
    unfold hl1, hl2, initP, HLayer.t, HLayer.hinitP.
    unfold horizInitP; intros.
    specialize (H i0); propositional.
    eauto using a.(initP_compat).
  Qed.
  End S.
End LayerImplLoopHT.
