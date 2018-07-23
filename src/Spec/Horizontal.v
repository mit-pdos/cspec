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
Require Import Spec.Modules.
Require Import Spec.Abstraction.
Require Import Spec.Movers.
Require Import Spec.Compile.
Require Import Spec.CompileLoop.
Require Import Spec.Protocol.

Require Import Coq.Program.Equality.


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

  Definition validIndexT := { i : indexT | indexValid i }.

  Inductive CheckResult :=
  | Missing
  | Present : validIndexT -> CheckResult
  .

  Inductive horizOpT : Type -> Type :=
  | Slice : forall (i : validIndexT) T (op : sliceOpT T), horizOpT T
  | CheckSlice : forall (i : indexT), horizOpT CheckResult
  .

  Record horizState := mk_horizState {
    HSMap : FMap.t indexT sliceState;
    HSValid : forall i, indexValid i -> FMap.In i HSMap;
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

  Theorem hget_hadd_eq_general : forall i s s',
      hget (hadd i s s') i = s.
  Proof.
    destruct i; intros.
    apply hget_hadd_eq.
  Qed.

  Theorem hget_hadd_ne : forall S s i i' H0 H1,
    i <> i' ->
    hget (hadd (exist _ i H0) s S) (exist _ i' H1) = hget S (exist _ i' H1).
  Proof.
    destruct S; simpl; intros.
    repeat match goal with
    | |- context[FMap.in_mapsto_get ?a ?b ?c] => destruct (FMap.in_mapsto_get a b c)
    end.
    eapply FMap.mapsto_add_ne in m; eauto.
    eapply FMap.mapsto_unique; eauto.
  Qed.

  Theorem hget_hadd_ne_general : forall i i' s S,
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

  Theorem hadd_hadd_eq : forall S s s' i H0 H1,
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

  Theorem hadd_hadd_ne : forall S s s' i i' H0 H1,
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

  Inductive sameSlice : CheckResult -> indexT -> Prop :=
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
      indexValid i ->
      exists s,
        FMap.MapsTo i s (HSMap S) /\
        initP s.

  Fixpoint SliceProc (i : validIndexT) `(p : proc sliceOpT T) : proc horizOpT T :=
    match p with
    | Call op => Call (Slice i op)
    | Ret v => Ret v
    | Bind p1 p2 => Bind (SliceProc i p1) (fun r => SliceProc i (p2 r))
    | Until cond p init => Until cond (fun x => SliceProc i (p x)) init
    | Atomic p => Atomic (SliceProc i p)
    | Spawn p => Spawn (SliceProc i p)
    end.

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

  Theorem SliceProc_spawn : forall i (p1: proc _ unit) T' (p2: proc _ T'),
      Spawn (SliceProc i p2) = SliceProc i p1 ->
      p1 = Spawn p2.
  Proof.
    intros.
    dependent destruction p1; simpl in *; intros; try congruence.
    invert H.
    eapply SliceProc_eq in H2.
    f_equal; auto.
  Qed.

End HorizontalComposition.

Arguments horizState indexT {cmp} indexValid sliceState.
Arguments horizStep indexT {cmp} indexValid {sliceOpT sliceState} sliceStep.
Arguments Slice {indexT indexValid sliceOpT} i {T}.
Arguments CheckSlice {indexT indexValid sliceOpT} i.
Arguments Missing {indexT indexValid}.


Ltac destruct_horizState :=
  match goal with
  | x : horizState _ _ _ |- _ => destruct x; simpl in *
  end.

Ltac destruct_validIndex :=
  match goal with
  | x : validIndexT _ |- _ => destruct x; simpl in *
  end.


Section HorizontalCompositionAbs.

  Variable indexT : Type.
  Context {cmp : Ordering indexT}.
  Variable indexValid : indexT -> Prop.

  Variable sliceOpT : Type -> Type.

  Variable sliceState1 : Type.
  Variable sliceStep1 : OpSemantics sliceOpT sliceState1.

  Variable sliceState2 : Type.
  Variable sliceStep2 : OpSemantics sliceOpT sliceState2.


  Variable absR : sliceState1 -> sliceState2 -> Prop.

  Definition horizAbsR (S1 : horizState indexT indexValid sliceState1)
                       (S2 : horizState indexT indexValid sliceState2) : Prop :=
    forall (i : indexT),
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
    op_abs horizAbsR (horizStep indexT indexValid sliceStep1) (horizStep indexT indexValid sliceStep2).
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
          + eapply FMap.mapsto_add_eq in H3; subst; eauto.
          + eapply FMap.mapsto_add_eq in H3; subst; eauto.
        - specialize (H0 i); intuition idtac.
          + eapply FMap.mapsto_add_ne in H0; eauto.
            specialize (H3 _ H0); deex; eauto.
          + eapply FMap.mapsto_add_ne in H0; eauto.
            specialize (H4 _ H0); deex; eauto.
      }
      {
        pose proof (@hget_mapsto _ _ _ _ idx s1).
        pose proof (@hget_mapsto _ _ _ _ idx s2).
        eapply H0 in H1; deex.
        replace s0 with (hget s2 idx) in * by ( eapply FMap.mapsto_unique; eauto ).
        eauto.
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

  Variable initP_ok :
    forall s1 s2,
      initP1 s1 ->
      absR s1 s2 ->
      initP2 s2.

  Theorem horizAbsR_initP_ok :
    forall s1 s2,
      horizInitP initP1 s1 ->
      horizAbsR s1 s2 ->
      horizInitP initP2 s2.
  Proof.
    unfold horizInitP, horizAbsR; intros.
    specialize (H _ H1); deex.
    eapply H0 in H; deex.
    eapply initP_ok in H2; eauto.
  Qed.

End HorizontalCompositionAbs.

Arguments horizAbsR indexT {cmp indexValid sliceState1 sliceState2} absR.


Section HorizontalCompositionMovers.

  Variable indexT : Type.
  Context {cmp : Ordering indexT}.
  Variable indexValid : indexT -> Prop.

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

  Theorem horiz_right_mover_ok :
    forall `(op : sliceOpT T),
      right_mover sliceStep op ->
      forall i,
        right_mover (horizStep indexT indexValid sliceStep) (Slice i op).
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
        enabled_stable (horizStep indexT indexValid sliceStep) T (Slice i op).
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

  Theorem horiz_left_mover_ok :
    forall `(op : sliceOpT T),
      left_mover sliceStep op ->
      forall i,
        left_mover (horizStep indexT indexValid sliceStep) (Slice i op).
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

  Theorem horiz_left_mover_pred_ok :
    forall `(op : sliceOpT T) P,
      left_mover_pred sliceStep op P ->
      forall i,
        left_mover_pred (horizStep indexT indexValid sliceStep) (Slice i op)
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
    atomic_exec (horizStep indexT indexValid sliceStep) p0 tid S v S' evs ->
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

  Lemma hadd_hget_eq' : forall (i: validIndexT indexValid) (s: horizState _ _ sliceState),
      s = hadd i (hget s i) s.
  Proof.
    intros.
    destruct_validIndex.
    rewrite hadd_hget_eq; auto.
  Qed.

  Hint Resolve hadd_hget_eq'.

  Lemma exec_tid_slice :
    forall S1 S2 tid `(p : proc _ T) r spawned evs,
      exec_tid (horizStep indexT indexValid sliceStep) tid S1 p S2 r spawned evs ->
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

  Lemma exec_any_slice :
    forall S1 S2 tid `(p : proc _ T) r,
      exec_any (horizStep indexT indexValid sliceStep) tid S1 p r S2 ->
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

  Lemma exec_others_slice :
    forall S1 S2 tid,
      exec_others (horizStep indexT indexValid sliceStep) tid S1 S2 ->
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

  Lemma horiz_left_movers :
    forall `(p : proc _ T) P,
      left_movers sliceStep P p ->
      forall i,
        left_movers (horizStep indexT indexValid sliceStep)
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


  Theorem horiz_ysa_movers :
    forall `(p : proc _ T),
      ysa_movers sliceStep p ->
      forall i,
        ysa_movers (horizStep indexT indexValid sliceStep) (SliceProc i p).
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

Module Type HIndex.
  Axiom indexT : Type.
  Axiom indexValid : indexT -> Prop.
  Axiom indexCmp : Ordering indexT.
End HIndex.

Module HOps (o : Ops) (i : HIndex) <: Ops.
  Definition Op := horizOpT i.indexValid o.Op.
End HOps.

Module HState (s : State) (i : HIndex) <: State.
  Definition State := @horizState i.indexT i.indexCmp i.indexValid s.State.
  Definition initP : State -> Prop :=
    horizInitP s.initP.
End HState.

Module HLayer (o : Ops) (s : State) (l : Layer o s) (i : HIndex).
  Definition step := @horizStep i.indexT i.indexCmp i.indexValid _ _ l.step.
End HLayer.

Module HProtocol (o : Ops) (s : State) (p : Protocol o s) (i : HIndex).
  Module ho := HOps o i.
  Module hs := HState s i.
  Definition step_allow T (hop : ho.Op T) (tid : nat) (S : hs.State) : Prop :=
    match hop with
    | Slice i op =>
      p.step_allow op tid (hget S i)
    | CheckSlice i =>
      True
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
    @horizAbsR i.indexT i.indexCmp i.indexValid _ _ a.absR.

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

  Definition compile_op T (op : ho2.Op T) : proc ho1.Op T :=
    match op with
    | Slice i op => SliceProc i (a.compile_op op)
    | CheckSlice i => Call (CheckSlice i)
    end.

  Theorem compile_op_no_atomics : forall T (op : ho2.Op T),
    no_atomics (compile_op op).
  Proof.
    destruct op; simpl; eauto.
    pose proof (a.compile_op_no_atomics op).
    generalize dependent H.
    generalize (a.compile_op op).
    clear.
    induction 1; simpl; eauto.
  Qed.

  Theorem ysa_movers : forall T (op : ho2.Op T),
    ysa_movers hl1.step (compile_op op).
  Proof.
    destruct op; simpl; eauto.
    eapply horiz_ysa_movers.
    eapply a.ysa_movers.
  Qed.

  Theorem compile_correct :
    compile_correct compile_op hl1.step hl2.step.
  Proof.
    intro; intros.
    destruct op; simpl in *.
    - eapply atomic_exec_horizStep in H; eauto; deex.
      eapply a.compile_correct in H.
      econstructor; eauto.
    - repeat atomic_exec_inv.
      inversion H5; clear H5; subst; repeat sigT_eq.
      econstructor; eauto.
  Qed.

  Existing Instance i.indexCmp.

  Hint Rewrite hget_hadd_eq_general : h.
  Hint Rewrite hget_hadd_ne_general using solve [ auto ] : h.

  Lemma step_high_to_step_low :
    forall s s' (i: validIndexT i.indexValid) T (op: hp.ho.Op T) tid r evs,
      restricted_step hl1raw.step hp.step_allow op tid s r s' evs ->
      (exists (op': o1.Op T) r' evs',
          restricted_step l1raw.step p.step_allow op' tid (hget s i) r' (hget s' i) evs') \/
      hget s i = hget s' i.
  Proof.
    intros.
    unfold restricted_step in *; propositional.
    unfold hp.step_allow, hl1raw.step in *.
    invert H0; clear H0.
    - destruct (i == idx); subst;
        autorewrite with h;
        eauto 10.
    - eauto.
  Qed.

  Lemma exec_ops_high : forall s s' (i: validIndexT i.indexValid),
      exec_ops (restricted_step hl1raw.step hp.step_allow) s s' ->
      exec_ops (restricted_step l1raw.step p.step_allow) (hget s i) (hget s' i).
  Proof.
    unfold exec_ops; intros.
    induction H; propositional.
    reflexivity.

    transitivity (hget y i); auto.
    eapply step_high_to_step_low with (i:=i) in H;
      (intuition propositional);
      eauto.
    - econstructor; [ | reflexivity ].
      descend; eauto.
    - replace (hget y i).
      reflexivity.
  Qed.

  Theorem op_follows_protocol : forall tid s `(op : ho2.Op T),
    follows_protocol_proc hl1raw.step hp.step_allow tid s (compile_op op).
  Proof.
    destruct op; simpl.
    - pose proof (a.op_follows_protocol tid (hget s i) op).
      generalize dependent (a.compile_op op); intros; clear dependent op.
      remember (hget s i).
      generalize dependent s.
      generalize dependent i.
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
                        follows_protocol_proc hl1raw.step hp.step_allow
                                              tid' s0 (SliceProc i p)).
        eauto.
        rename H into Hspawn.
        unfold spawn_follows_protocol; intros.
        specialize (H1 tid' ltac:(auto)).
        specialize (H0 tid' ltac:(auto)).
        specialize (Hspawn tid' ltac:(auto)).

        assert (exec_ops (restricted_step l1raw.step p.step_allow)
                         (hget s0 i) (hget s' i)).
        eapply exec_ops_high; eauto.
        eauto.
    - constructor; constructor.
  Qed.

  Theorem allowed_stable :
    forall `(op : ho1.Op T) `(op' : ho1.Op T') tid tid' s s' r evs,
      tid <> tid' ->
      hp.step_allow op tid s ->
      hl1.step op' tid' s r s' evs ->
      hp.step_allow op tid s'.
  Proof.
    destruct op, op'; eauto.
    {
      intros.
      simpl in *.
      inversion H1; clear H1; subst; repeat sigT_eq.
      pose (i.indexCmp).
      repeat destruct_validIndex.
      destruct (x == x0); subst.
      - replace i0 with i in * by apply proof_irrelevance.
        rewrite hget_hadd_eq.
        eapply a.allowed_stable; eauto.
      - rewrite hget_hadd_ne in * by eauto.
        eauto.
    }
    {
      intros.
      inversion H1; subst; eauto.
    }
  Qed.

  Theorem raw_step_ok :
    forall `(op : ho1.Op T) tid s r s' evs,
      restricted_step hl1raw.step hp.step_allow op tid s r s' evs ->
      hl1.step op tid s r s' evs.
  Proof.
    destruct op.
    - unfold restricted_step; intuition idtac.
      inversion H1; clear H1; subst; repeat sigT_eq.
      econstructor; eauto.
      eapply a.raw_step_ok.
      constructor; eauto.
    - unfold restricted_step; intuition idtac.
      inversion H1; clear H1; subst; repeat sigT_eq.
      econstructor; eauto.
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

  Definition compile_op T (op : ho2.Op T) : proc ho1.Op T :=
    match op with
    | Slice i op => SliceProc i (a.compile_op op)
    | CheckSlice i => Call (CheckSlice i)
    end.

  Theorem compile_op_no_atomics : forall T (op : ho2.Op T),
    no_atomics (compile_op op).
  Proof.
    destruct op; simpl; eauto.
    pose proof (a.compile_op_no_atomics op).
    generalize dependent H.
    generalize (a.compile_op op).
    clear.
    induction 1; simpl; eauto.
  Qed.

  Theorem ysa_movers : forall T (op : ho2.Op T),
    ysa_movers hl1.step (compile_op op).
  Proof.
    destruct op; simpl; eauto.
    eapply horiz_ysa_movers.
    eapply a.ysa_movers.
  Qed.

  Theorem compile_correct :
    compile_correct compile_op hl1.step hl2.step.
  Proof.
    intro; intros.
    destruct op; simpl in *.
    - eapply atomic_exec_horizStep in H; eauto; deex.
      eapply a.compile_correct in H.
      econstructor; eauto.
    - repeat atomic_exec_inv.
      inversion H5; clear H5; subst; repeat sigT_eq.
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

  Definition compile_op T (op : ho2.Op T) :
    (option T -> ho1.Op T) * (T -> bool) * option T :=
    match op with
    | Slice idx op' =>
      let '(p, cond, i) := a.compile_op op' in
        ((fun x => Slice idx (p x)), cond, i)
    | CheckSlice idx =>
      ((fun x => CheckSlice idx),
        fun _ => true,
        None)
    end.

  Theorem noop_or_success :
    noop_or_success compile_op hl1.step hl2.step.
  Proof.
    intro; intros.
    destruct opM; simpl in *.
    {
      destruct (a.compile_op op) eqn:He.
      destruct p.
      inversion H; clear H; subst.
      inversion H0; clear H0; subst; repeat sigT_eq.
      edestruct a.noop_or_success; eauto.
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

End LayerImplLoopHT.
