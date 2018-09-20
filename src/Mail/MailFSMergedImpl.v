Require Import CSPEC.
Require Import MailServerAPI.
Require Import MailFSMergedAPI.
Require Import MailFSPathAPI.
Require Import MailFSPathAbsAPI.


Module MailFSMergedAbsImpl' <:
  HLayerImplAbsT MailFSPathHOp
    MailFSMergedState   MailFSMergedAbsAPI
    MailFSPathAbsHState MailFSPathHAPI.

  Definition absR (s1 : MailFSMergedState.State) (s2 : MailFSPathAbsHState.State) :=
    forall u,
      UserIdx.indexValid u ->
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
    - specialize (H u0 H0); clear H0; intuition idtac.
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

    - specialize (H u0 H0); clear H0; simpl in *; intuition idtac.
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
    - specialize (H u0 H0); clear H0; simpl in *; intuition idtac.
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

    - specialize (H u0 H0); clear H0; simpl in *; intuition idtac.
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

  Theorem absR_not_In :
    forall fs lock s2 u dir fn P,
      absR (MailFSMergedState.mk_state fs lock) s2 ->
      (~ FMap.In (u, dir, fn) fs) ->
      ~ FMap.In (dir, fn)
        (MailFSPathAbsState.fs (hget s2 (exist _ u P))).
  Proof.
    intros.
    specialize (H u P); simpl in *; intuition idtac.
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

  Theorem absR_In :
    forall fs lock s2 u dir fn P,
      absR (MailFSMergedState.mk_state fs lock) s2 ->
      FMap.In (u, dir, fn) fs ->
      FMap.In (dir, fn)
        (MailFSPathAbsState.fs (hget s2 (exist _ u P))).
  Proof.
    intros.
    specialize (H u P); simpl in *; intuition idtac.
    apply FMap.in_mapsto_exists in H0; deex.
    eapply H3 in H0; deex.

    pose proof hget_mapsto.
    specialize (H4 _ _ _ _ (exist _ u P) s2).
    simpl in H4.

    eapply FMap.mapsto_unique in H0; try eassumption.
    unfold UserIdx.indexValid in *. unfold UserIdx.indexT. rewrite H0.

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
    specialize (H u P); simpl in *; intuition idtac.
    unfold FMap.is_permutation_key in *; split; intros.
    - eapply H0 in H2; clear H0.
      unfold drop_dirname in H2.
      unfold filter_dir in H2.
      unfold MailFSPathAbsAPI.drop_dirname.
      unfold MailFSPathAbsAPI.filter_dir.
      eapply FMap.map_keys_in' in H2; deex.
      eapply FMap.filter_in in H0 as H0'.
      eapply FMap.filter_holds in H0.
      destruct k'.
      destruct p.

      pose proof FMap.map_keys_in as Hx.
      specialize (Hx _ _ string _ _ (fun '(_, fn) => fn) (s1, s)).
      eapply Hx; clear Hx.

      destruct ((s0, s1) == (u, dir)); try congruence.
      inversion e; clear e; subst.

      eapply FMap.filter_complete.
      eapply FMap.in_mapsto_exists in H0'; deex.
      eapply H3 in H2; deex.
      eapply mapsto_to_hget in H2.
      rewrite H2 in *.
      eapply FMap.mapsto_in; eauto.

      destruct (dir == dir); eauto.

    - eapply H0; clear H0.
      eapply MailFSPathAbsAPI.drop_dirname_filter_dir in H2.

      eapply FMap.in_mapsto_exists in H2; deex.
      eapply H1 in H0; eauto.
      unfold drop_dirname.
      unfold filter_dir.

      pose proof FMap.map_keys_in as Hx.
      specialize (Hx _ _ string _ _ (fun '(_, fn) => fn) ((u, dir), x)).
      eapply Hx; clear Hx.

      eapply FMap.filter_complete.
      eapply FMap.mapsto_in; eauto.
      destruct ((u, dir) == (u, dir)); eauto.
  Qed.

  Theorem absR_locked :
    forall fs locked s2 u v P,
      absR (MailFSMergedState.mk_state fs locked) s2 ->
      FMap.MapsTo u v locked ->
      MailFSPathAbsState.locked (hget s2 (exist _ u P)) = v.
  Proof.
    intros.
    specialize (H u P); simpl in *; intuition idtac.
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
    - specialize (H u0 H0); clear H0; simpl in *; intuition idtac.
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

    - specialize (H u0 H0); clear H0; simpl in *; intuition idtac.
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
    pose proof H0 as Hvalid.
    eapply HSValid in H0.
    eapply FMap.in_mapsto_exists in H0; deex.
    specialize (H u Hvalid); simpl in *; intuition idtac.
    eapply H1 in H0; intuition idtac.
    eapply FMap.mapsto_in; eauto.
  Qed.

  Hint Resolve absR_fs_add.
  Hint Resolve absR_fs_remove.
  Hint Resolve absR_MapsTo.
  Hint Resolve absR_not_In.
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

  Fixpoint fmap_constant A {Acmp:Ordering A} V (v:V) (l: list A) : FMap.t A V :=
    match l with
    | nil => FMap.empty
    | x::xs => FMap.add x v (fmap_constant v xs)
    end.

  Theorem fmap_constant_all : forall A (Acmp:Ordering A) V (v:V) (l: list A),
      forall a, List.In a l ->
           FMap.MapsTo a v (fmap_constant v l).
  Proof.
    induction l; simpl; intuition (subst; eauto).
    destruct (cmp_dec a a0); subst.
    apply FMap.add_mapsto.
    apply FMap.mapsto_add_ne'; eauto.
  Qed.

  Definition fmap_all : forall V (v:V),
      {m:FMap.t UserIdx.indexT V |
       forall i, UserIdx.indexValid i -> FMap.MapsTo i v m}.
    intros.
    unfold UserIdx.indexValid.
    exists (fmap_constant v (UserIdx.validUsers)); intros.
    auto using fmap_constant_all.
  Defined.

  Definition initP_map (s1: MailFSMergedState.State) :
    {s2: MailFSPathAbsHState.State | MailFSMergedAPI.initP s1 ->
                                 absR s1 s2 /\ MailFSPathAbsHAPI.initP s2}.
  Proof.
    unfold MailFSMergedAPI.initP, MailFSPathAbsHAPI.initP, absR,
    MailFSMergedState.initP,
    horizInitP, MailFSPathAbsAPI.initP, MailFSPathAbsState.initP;
    intros.
    destruct s1; simpl.
    unshelve eexists
             {| HSMap :=
                  proj1_sig (fmap_all
                               {| MailFSPathAbsState.fs := FMap.empty;
                                  MailFSPathAbsState.locked := false; |}) |};
      match goal with
      | [ |- context[fmap_all ?v] ] => destruct (fmap_all v); simpl
      end.
    intros.
    eapply FMap.mapsto_in; eauto.
    (intuition eauto); propositional;
      repeat match goal with
             | [ H: UserIdx.indexValid _,
                    H': forall u, UserIdx.indexValid u -> _ |- _ ] =>
               specialize (H' _ H)
             | _ => FMap.mapsto_unique
             end;
      simpl;
      eauto.
  Qed.

End MailFSMergedAbsImpl'.


Module MailFSMergedAbsImpl :=
 HLayerImplAbs MailFSPathHOp
    MailFSMergedState   MailFSMergedAbsAPI
    MailFSPathAbsHState MailFSPathHAPI
    MailFSMergedAbsImpl'.


Module MailFSMergedOpImpl' <:
  LayerImplMoversT
    MailFSMergedState
    MailFSMergedOp MailFSMergedAPI
    MailFSPathHOp  MailFSMergedAbsAPI.

  Import MailFSPathOp.

  (* START CODE *)

  Definition compile_op T (op : MailFSPathHOp.Op T) : proc MailFSMergedOp.Op T :=
    match op with
    | Slice (exist _ u _) op' =>
      match op' with
      | Link (srcdir, srcfn) (dstdir, dstfn) =>
        Call (MailFSMergedOp.Link (u, srcdir, srcfn) (u, dstdir, dstfn))
      | List dir =>
        Call (MailFSMergedOp.List (u, dir))
      | Read (dir, fn) =>
        Call (MailFSMergedOp.Read (u, dir, fn))
      | Create (dir, fn) =>
        Call (MailFSMergedOp.Create (u, dir, fn))
      | Write (dir, fn) data =>
        Call (MailFSMergedOp.Write (u, dir, fn) data)
      | Unlink (dir, fn) =>
        Call (MailFSMergedOp.Unlink (u, dir, fn))
      | Ext extop =>
        Call (MailFSMergedOp.Ext extop)
      | Lock =>
        Call (MailFSMergedOp.Lock u)
      | Unlock =>
        Call (MailFSMergedOp.Unlock u)
      | GetTID =>
        Call (MailFSMergedOp.GetTID)
      | Random =>
        Call (MailFSMergedOp.Random)
      end
    | CheckSlice u =>
      Call (MailFSMergedOp.Exists u)
    end.

  (* END CODE *)

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

  Definition initP_compat : forall s,
      MailFSMergedAPI.initP s -> MailFSMergedAbsAPI.initP s :=
    ltac:(auto).

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
