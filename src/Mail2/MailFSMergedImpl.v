Require Import POCS.
Require Import MailServerAPI.
Require Import MailFSMergedAPI.
Require Import MailFSPathAPI.
Require Import MailFSPathAbsAPI.


Module MailFSMergedAbsImpl' <:
  LayerImplAbsT MailFSPathHOp
    MailFSMergedState   MailFSMergedAbsAPI
    MailFSPathAbsHState MailFSPathHAPI.

  Definition absR (s1 : MailFSMergedState.State) (s2 : MailFSPathAbsHState.State) :=
    forall u,
      ( forall s2',
        FMap.MapsTo u s2' (HSMap s2) ->
          FMap.MapsTo u (MailFSPathAbsState.locked s2') (MailFSMergedState.locked s1) /\
          ( forall dir fn f,
            FMap.MapsTo (dir, fn) f (MailFSPathAbsState.fs s2') ->
            FMap.MapsTo (u, dir, fn) f (MailFSMergedState.fs s1) ) ) /\
      ( forall locked,
        FMap.MapsTo u locked (MailFSMergedState.locked s1) ->
          exists s2',
            FMap.MapsTo u s2' (HSMap s2) /\
            MailFSPathAbsState.locked s2' = locked ) /\
      ( forall dir fn f,
        FMap.MapsTo (u, dir, fn) f (MailFSMergedState.fs s1) ->
          exists s2',
            FMap.MapsTo u s2' (HSMap s2) /\
            FMap.MapsTo (dir, fn) f (MailFSPathAbsState.fs s2') ).

  Hint Resolve FMap.add_mapsto.
  Hint Resolve FMap.mapsto_add_ne'.
  Hint Constructors MailFSPathAPI.xstep.

  Theorem mapsto_hadd_ne :
    forall u0 u1 T (s : T) indexValid S v P,
      u0 <> u1 ->
      FMap.MapsTo u0 s (HSMap (hadd (exist _ u1 P) v S)) ->
      FMap.MapsTo u0 s (HSMap (indexValid:=indexValid) S).
  Proof.
    destruct S.
    unfold hadd.
    simpl; intros.
    eapply FMap.mapsto_add_ne; eauto.
  Qed.

  Theorem mapsto_hadd_ne' :
    forall u0 u1 T (s : T) indexValid S v P,
      u0 <> u1 ->
      FMap.MapsTo u0 s (HSMap (indexValid:=indexValid) S) ->
      FMap.MapsTo u0 s (HSMap (hadd (exist _ u1 P) v S)).
  Proof.
    destruct S.
    unfold hadd.
    simpl; intros.
    eapply FMap.mapsto_add_ne'; eauto.
  Qed.

  Theorem mapsto_hadd_eq :
    forall u T (s : T) indexValid S s' P,
      FMap.MapsTo u s (HSMap (indexValid:=indexValid)
                             (hadd (exist _ u P) s' S)) ->
      s = s'.
  Proof.
    destruct S.
    unfold hadd.
    simpl; intros.
    eapply FMap.mapsto_add in H; eauto.
  Qed.

  Theorem mapsto_hadd_eq' :
    forall u T (s : T) indexValid S P,
      FMap.MapsTo u s (HSMap (indexValid:=indexValid)
                             (hadd (exist _ u P) s S)).
  Proof.
    destruct S.
    unfold hadd.
    simpl; intros.
    eapply FMap.add_mapsto.
  Qed.

  Theorem mapsto_to_hget :
    forall `(v : T) indexValid u S P,
      FMap.MapsTo u v (HSMap (indexValid:=indexValid) S) ->
      v = hget S (exist _ u P).
  Proof.
    intros.
    eapply FMap.mapsto_unique; eauto.
    eapply hget_mapsto'.
  Qed.

  Hint Resolve hget_mapsto'.
  Hint Resolve mapsto_hadd_eq'.

  Theorem absR_fs_add :
    forall fs lock s2 u dir fn data P,
      absR (MailFSMergedState.mk_state fs lock) s2 ->
      absR (MailFSMergedState.mk_state (FMap.add (u, dir, fn) data fs) lock)
           (hadd (exist _ u P)
                 (MailFSPathAbsState.mk_state
                   (FMap.add (dir, fn) data
                     (MailFSPathAbsState.fs (hget s2 (exist _ u P))))
                   (MailFSPathAbsState.locked (hget s2 (exist _ u P)))) s2).
  Proof.
    unfold absR; simpl; intros.
    destruct (u == u0); subst.
    - specialize (H u0); intuition idtac.
      + eapply mapsto_hadd_eq in H1; subst; simpl in *.
        eapply H0; eauto.
      + eapply mapsto_hadd_eq in H1; subst; simpl in *.
        destruct ((dir0, fn0) == (dir, fn)).
        * inversion e; clear e; subst.
          eapply FMap.mapsto_add in H3; subst.
          eapply FMap.add_mapsto.
        * eapply FMap.mapsto_add_ne in H3; eauto.
          eapply FMap.mapsto_add_ne'; try congruence.
          eapply H0; eauto.
          eauto.
      + edestruct H; eauto; intuition idtac.
        eexists; split.
        eapply mapsto_hadd_eq'.
        eapply mapsto_to_hget in H4.
        rewrite H4 in *.
        simpl; eauto.
      + destruct ((dir0, fn0) == (dir, fn)).
        * inversion e; clear e; subst.
          eapply FMap.mapsto_add in H1; subst.
          eexists; split; eauto.
          simpl; eauto.
        * eapply FMap.mapsto_add_ne in H1; try congruence.
          edestruct H2; eauto; intuition idtac.
          eexists; split.
          eapply mapsto_hadd_eq'.
          eapply mapsto_to_hget in H4.
          rewrite H4 in *.
          simpl; eauto.

    - specialize (H u0); simpl in *; intuition idtac.
      + eapply mapsto_hadd_ne in H1; eauto.
        eapply H0 in H1.
        intuition eauto.
      + eapply mapsto_hadd_ne in H1; eauto.
        eapply H0 in H1.
        eapply FMap.mapsto_add_ne'; try congruence.
        intuition eauto.
      + eapply H in H1; deex.
        eexists; intuition eauto.
        eapply mapsto_hadd_ne'; eauto.
      + eapply FMap.mapsto_add_ne in H1; try congruence.
        eapply H2 in H1; deex.
        eexists; intuition eauto.
        eapply mapsto_hadd_ne'; eauto.
  Qed.

  Theorem absR_fs_remove :
    forall fs lock s2 u dir fn P,
      absR (MailFSMergedState.mk_state fs lock) s2 ->
      absR (MailFSMergedState.mk_state (FMap.remove (u, dir, fn) fs) lock)
           (hadd (exist _ u P)
                 (MailFSPathAbsState.mk_state
                   (FMap.remove (dir, fn)
                     (MailFSPathAbsState.fs (hget s2 (exist _ u P))))
                   (MailFSPathAbsState.locked (hget s2 (exist _ u P)))) s2).
  Proof.
    unfold absR; simpl; intros.
    destruct (u == u0); subst.
    - specialize (H u0); simpl in *; intuition idtac.
      + eapply mapsto_hadd_eq in H1; subst; simpl in *.
        eapply H0; eauto.
      + eapply mapsto_hadd_eq in H1; subst; simpl in *.
        eapply FMap.mapsto_remove in H3; intuition.
        eapply FMap.mapsto_remove_ne; try congruence.
        eapply H0; eauto.
        eauto.
      + edestruct H; eauto; intuition idtac.
        eexists; split.
        eapply mapsto_hadd_eq'.
        eapply mapsto_to_hget in H4.
        rewrite H4 in *.
        simpl; eauto.
      + eapply FMap.mapsto_remove in H1; intuition.
        edestruct H2; eauto; intuition idtac.
        eexists; split.
        eapply mapsto_hadd_eq'.
        simpl.
        eapply FMap.mapsto_remove_ne.
        eapply mapsto_to_hget in H5.
        rewrite H5 in *.
        simpl; eauto.
        intro Hx; inversion Hx; clear Hx; subst.
        eauto.

    - specialize (H u0); simpl in *; intuition idtac.
      + eapply mapsto_hadd_ne in H1; eauto.
        eapply H0 in H1.
        intuition eauto.
      + eapply mapsto_hadd_ne in H1; eauto.
        eapply H0 in H1.
        eapply FMap.mapsto_remove_ne; try congruence.
        intuition eauto.
      + eapply H in H1; deex.
        eexists; intuition eauto.
        eapply mapsto_hadd_ne'; eauto.
      + eapply FMap.mapsto_remove in H1; intuition idtac.
        eapply H2 in H4; deex.
        eexists; intuition eauto.
        eapply mapsto_hadd_ne'; eauto.
  Qed.

  Theorem absR_MapsTo :
    forall fs lock s2 u dir fn data P,
      absR (MailFSMergedState.mk_state fs lock) s2 ->
      FMap.MapsTo (u, dir, fn) data fs ->
      FMap.MapsTo (dir, fn) data
        (MailFSPathAbsState.fs (hget s2 (exist _ u P))).
  Proof.
    intros.
    specialize (H u); simpl in *; intuition idtac.
    eapply H3 in H0; clear H3; deex.
    pose proof hget_mapsto.
    specialize (H3 _ _ _ _ (exist _ u P) s2); simpl in *.
    eapply FMap.mapsto_unique in H3; [ | exact H0 ].
    subst.
    eauto.
  Qed.

  Theorem absR_In :
    forall fs lock s2 u dir fn P,
      absR (MailFSMergedState.mk_state fs lock) s2 ->
      (~ FMap.In (u, dir, fn) fs) ->
      ~ FMap.In (dir, fn)
        (MailFSPathAbsState.fs (hget s2 (exist _ u P))).
  Proof.
    intros.
    specialize (H u); simpl in *; intuition idtac.
    apply H0; clear H0.
    apply FMap.in_mapsto_exists in H1; deex.
    edestruct H2.
    {
      pose proof hget_mapsto.
      specialize (H1 _ _ _ _ (exist _ u P) s2).
      simpl in H1.
      eauto.
    }
    eapply FMap.mapsto_in; eauto.
  Qed.

  Theorem absR_is_permutation_key :
    forall fs lock s2 u dir r P,
      absR (MailFSMergedState.mk_state fs lock) s2 ->
      FMap.is_permutation_key r (drop_dirname (filter_dir (u, dir) fs)) ->
      FMap.is_permutation_key r (MailFSPathAbsAPI.drop_dirname
        (MailFSPathAbsAPI.filter_dir dir
          (MailFSPathAbsState.fs
            (hget s2 (exist _ u P))))).
  Proof.
    intros.
    specialize (H u); simpl in *; intuition idtac.
    unfold FMap.is_permutation_key in *; split; intros.
    - eapply H0 in H2; clear H0.
      admit.

    - eapply H0; clear H0.
      eapply MailFSPathAbsAPI.drop_dirname_filter_dir in H2.
      admit.

  Admitted.

  Theorem absR_locked :
    forall fs locked s2 u v P,
      absR (MailFSMergedState.mk_state fs locked) s2 ->
      FMap.MapsTo u v locked ->
      MailFSPathAbsState.locked (hget s2 (exist _ u P)) = v.
  Proof.
    intros.
    specialize (H u); simpl in *; intuition idtac.
    eapply H in H0; deex.
    f_equal.
    eapply FMap.mapsto_unique; try eassumption.
    pose proof hget_mapsto.
    specialize (H2 _ _ _ _ (exist _ u P) s2).
    eauto.
  Qed.

  Theorem absR_locked_add :
    forall fs locked s2 u v P,
      absR (MailFSMergedState.mk_state fs locked) s2 ->
      absR (MailFSMergedState.mk_state fs (FMap.add u v locked))
           (hadd (exist _ u P)
                 (MailFSPathAbsState.mk_state
                   (MailFSPathAbsState.fs (hget s2 (exist _ u P)))
                   v) s2).
  Proof.
    unfold absR; simpl; intros.
    destruct (u == u0); subst.
    - specialize (H u0); simpl in *; intuition idtac.
      + eapply mapsto_hadd_eq in H1; subst; simpl in *.
        eauto.
      + eapply mapsto_hadd_eq in H1; subst; simpl in *.
        eapply H0; eauto.
        eauto.
      + eapply FMap.mapsto_add in H1; subst.
        eexists; split; eauto.
      + edestruct H2; eauto; intuition idtac.
        eexists; split.
        eapply mapsto_hadd_eq'.
        eapply mapsto_to_hget in H4.
        rewrite H4 in *.
        simpl; eauto.

    - specialize (H u0); simpl in *; intuition idtac.
      + eapply mapsto_hadd_ne in H1; eauto.
        eapply H0 in H1.
        eapply FMap.mapsto_add_ne'; eauto.
        intuition eauto.
      + eapply mapsto_hadd_ne in H1; eauto.
        eapply H0 in H1.
        intuition eauto.
      + eapply FMap.mapsto_add_ne in H1; eauto.
        eapply H in H1; deex.
        eexists; intuition eauto.
        eapply mapsto_hadd_ne'; eauto.
      + eapply H2 in H1; deex.
        eexists; intuition eauto.
        eapply mapsto_hadd_ne'; eauto.
  Qed.

  Theorem absR_valid_in_locked : forall fs locked s2 u,
    absR (MailFSMergedState.mk_state fs locked) s2 ->
    UserIdx.indexValid u ->
    FMap.In u locked.
  Proof.
    destruct s2; intros.
    eapply HSValid in H0.
    eapply FMap.in_mapsto_exists in H0; deex.
    specialize (H u); simpl in *; intuition idtac.
    eapply H1 in H0; intuition idtac.
    eapply FMap.mapsto_in; eauto.
  Qed.

  Hint Resolve absR_fs_add.
  Hint Resolve absR_fs_remove.
  Hint Resolve absR_MapsTo.
  Hint Resolve absR_In.
  Hint Resolve absR_is_permutation_key.
  Hint Resolve absR_locked_add.
  Hint Resolve absR_valid_in_locked.

  Ltac split_path_abs_state :=
    match goal with
    | |- MailFSPathAPI.xstep _ _ ?s _ _ _ =>
      replace s with (MailFSPathAbsState.mk_state
        (MailFSPathAbsState.fs s)
        (MailFSPathAbsState.locked s)) by ( destruct s; reflexivity )
    | _ => idtac
    end.

  Ltac nop_hadd_path_abs_state :=
    match goal with
    | |- absR _ (hadd _ (MailFSPathAbsState.mk_state
                          (MailFSPathAbsState.fs ?s)
                          (MailFSPathAbsState.locked ?s)) _) =>
      replace (MailFSPathAbsState.mk_state
                (MailFSPathAbsState.fs s) (MailFSPathAbsState.locked s))
        with s by ( destruct s; reflexivity );
      rewrite hadd_hget_eq;
      eassumption
    end.

  Theorem absR_ok :
    op_abs absR MailFSMergedAbsAPI.step MailFSPathHAPI.step.
  Proof.
    unfold op_abs; intros.
    unfold MailFSPathHAPI.step.
    unfold MailFSPathAPI.step.
    inversion H0; clear H0; subst; repeat sigT_eq.

    all: eexists.
    all: try solve [ split;
      [
      | econstructor;
        split_path_abs_state;
        try erewrite absR_locked by eauto;
        econstructor;
        eauto
      ];
      eauto
    ].

    all: try solve [ split;
      [ eassumption
      | rewrite <- hadd_hget_eq with (H0 := P) (H1 := P) at 2;
        econstructor;
        split_path_abs_state;
        econstructor;
        eauto
      ]
    ].

    all: try solve [ split; [ eauto | exfalso; eauto ] ].
  Qed.

  Theorem absInitP :
    forall s1 s2,
      MailFSMergedState.initP s1 ->
      absR s1 s2 ->
      MailFSPathAbsHState.initP s2.
  Proof.
    unfold MailFSPathAbsHState.initP.
    unfold MailFSMergedState.initP.
    unfold horizInitP.
    unfold absR.
    intros.

    eapply H in H1.
    eapply FMap.in_mapsto_exists in H1; deex.

    eapply H0 in H1; deex.
    eexists; split; eauto.

    unfold MailFSPathAbsState.initP; eauto.
  Qed.

End MailFSMergedAbsImpl'.


Module MailFSMergedAbsImpl :=
 LayerImplAbs MailFSPathHOp
    MailFSMergedState   MailFSMergedAbsAPI
    MailFSPathAbsHState MailFSPathHAPI
    MailFSMergedAbsImpl'.


Module MailFSMergedOpImpl' <:
  LayerImplMoversT
    MailFSMergedState
    MailFSMergedOp MailFSMergedAPI
    MailFSPathHOp  MailFSMergedAbsAPI.

  Import MailFSPathOp.

  Definition compile_op T (op : MailFSPathHOp.opT T) : proc MailFSMergedOp.opT T :=
    match op with
    | Slice (exist _ u _) op' =>
      match op' with
      | Link (srcdir, srcfn) (dstdir, dstfn) =>
        Op (MailFSMergedOp.Link (u, srcdir, srcfn) (u, dstdir, dstfn))
      | List dir =>
        Op (MailFSMergedOp.List (u, dir))
      | Read (dir, fn) =>
        Op (MailFSMergedOp.Read (u, dir, fn))
      | CreateWrite (dir, fn) data =>
        Op (MailFSMergedOp.CreateWrite (u, dir, fn) data)
      | Unlink (dir, fn) =>
        Op (MailFSMergedOp.Unlink (u, dir, fn))
      | Ext extop =>
        Op (MailFSMergedOp.Ext extop)
      | Lock =>
        Op (MailFSMergedOp.Lock u)
      | Unlock =>
        Op (MailFSMergedOp.Unlock u)
      | GetTID =>
        Op (MailFSMergedOp.GetTID)
      | Random =>
        Op (MailFSMergedOp.Random)
      end
    | CheckSlice u =>
      Op (MailFSMergedOp.Exists u)
    end.

  Ltac break_pairs :=
    match goal with
    | x : ?T * ?R |- _ => destruct x
    end.

  Theorem compile_op_no_atomics :
    forall `(op : _ T),
      no_atomics (compile_op op).
  Proof.
    destruct op; simpl; eauto.
    destruct op; compute; eauto.
    all: destruct_validIndex.
    all: repeat break_pairs; eauto.
  Qed.

  Ltac step_inv :=
    match goal with
    | H : MailFSMergedAbsAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : MailFSMergedAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    end; intuition idtac.

  Hint Extern 1 (MailFSMergedAbsAPI.step _ _ _ _ _ _) => econstructor.
  Hint Extern 1 (MailFSMergedAPI.step _ _ _ _ _ _) => econstructor.

  Theorem compile_correct :
    compile_correct compile_op MailFSMergedAPI.step MailFSMergedAbsAPI.step.
  Proof.
    unfold compile_correct; intros.
    destruct op.
    - destruct op.
      all: try destruct_validIndex.
      all: repeat break_pairs.
      all: atomic_exec_inv.
      all: repeat step_inv.
      all: eauto.
    - unfold UserIdx.indexT in *.
      atomic_exec_inv.
      step_inv; eauto.
  Qed.

  Theorem ysa_movers : forall `(op : _ T),
    ysa_movers MailFSMergedAPI.step (compile_op op).
  Proof.
    destruct op; simpl; eauto.
    destruct_validIndex.
    destruct op; simpl; repeat break_pairs; eauto 20.
  Qed.

End MailFSMergedOpImpl'.


Module MailFSMergedOpImpl :=
  LayerImplMovers
    MailFSMergedState
    MailFSMergedOp MailFSMergedAPI
    MailFSPathHOp  MailFSMergedAbsAPI
    MailFSMergedOpImpl'.

Module MailFSMergedImpl :=
  Link
    MailFSMergedOp MailFSMergedState   MailFSMergedAPI
    MailFSPathHOp  MailFSMergedState   MailFSMergedAbsAPI
    MailFSPathHOp  MailFSPathAbsHState MailFSPathHAPI
    MailFSMergedOpImpl MailFSMergedAbsImpl.
