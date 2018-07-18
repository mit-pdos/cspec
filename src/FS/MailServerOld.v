Require Import CSPEC.
Require Import FSModel.
Require Import LinkAPI.
Require Import FSAPI.
Require Import MailServerAPI.
Require Import MailServerLayers.

Import ListNotations.
Require Import String.
Open Scope string.
Open Scope list.

Hint Constructors mailfs_step_allowed.

Axiom tmpdir_not_maildir : forall user, tmpdir = (maildir ++ [user])%list -> False.
Hint Resolve tmpdir_not_maildir.


Hint Resolve starts_with_tid_ne.

Instance invariant_proper :
  Proper (FSEquiv ==> iff) invariant.
Proof.
  intros ? ? ?; subst.
  unfold invariant, unique_pathname_root; intuition idtac; repeat deex.
  - exists node.
    rewrite <- H in *.
    split; auto.
    intros.
    rewrite <- H in *.
    auto.
  - eexists node.
    rewrite H in *.
    split; auto.
    intros.
    rewrite H in *; auto.
Qed.

Lemma path_eval_root_create: forall fs pn dirnum h name,
    does_not_exist fs dirnum name ->
    path_eval_root fs pn (DirNode dirnum) ->
    path_eval_root (create_file dirnum h name fs) pn (DirNode dirnum ).
Proof.
  intros.
  eapply path_eval_root_upd_file in H0.
  eapply path_eval_root_add_link in H0; eauto.
Qed.

(*
Lemma FS_path_evaluates_eq: forall fs fs' startdir pn node node',
    FSEquiv fs fs' ->
    path_evaluates fs (DirNode startdir) pn node ->
    path_evaluates fs' (DirNode startdir) pn node' ->
    node = node'.
Admitted.

Require Import Bool.
Require Import Ascii.

Definition eq_ascii (a1 a2 : ascii) :=
  match a1, a2 with
  | Ascii b1 b2 b3 b4 b5 b6 b7 b8, Ascii c1 c2 c3 c4 c5 c6 c7 c8 =>
    (eqb b1 c1) && (eqb b2 c2) && (eqb b3 c3) && (eqb b4 c4) &&
    (eqb b5 c5) && (eqb b6 c6) && (eqb b7 c7) && (eqb b8 c8)
  end.

Fixpoint eq_string (s1 s2 : string) :=
  match s1, s2 with
  | EmptyString,  EmptyString  => true
  | String x1 s1, String x2 s2 => eq_ascii x1 x2 && eq_string s1 s2
  | _, _                       => false
  end.

Definition match_dirent from s l :=
  eq_string s (LinkName l) && (beq_nat from (LinkFrom l)).

Definition dirents fs from name :=
  Graph.filter (match_dirent from name) fs.

Definition chooseone dirents := Graph.choose dirents.

Fixpoint path pn (fs:Graph.t) dir: Graph.t :=
  match pn with
  | nil => Graph.empty
  | e :: pn' =>
    let s := dirents fs dir e in
    match chooseone s with
    | None => Graph.empty
    | Some l =>
      match (LinkTo l) with
      | DirNode n => Graph.add l (path pn' fs n)
        (* XXX symbolic links *)                      
      | _ => Graph.empty
      end
    end
  end.
 *)

Lemma path_unique_eq: forall fs dirnum pn node',
    unique_pathname_root fs pn ->
    path_eval_root fs pn (DirNode dirnum) ->
    path_eval_root fs pn node' ->
    node' = DirNode dirnum.
Proof.
  intros.
  unfold unique_pathname_root in *.
  deex.
  specialize (H2 (DirNode dirnum)) as Hx.
  specialize (Hx H0).
  subst.
  specialize (H2 node' H1); auto.
Qed.

Lemma path_unique_create_inum_eq: forall fs pn dirnum dirnum0 h name,
    unique_pathname_root fs pn ->
    does_not_exist fs dirnum0 name ->
    file_handle_unused fs h ->
    file_handle_valid fs h ->
    unique_pathname_root (create_file dirnum0 h name fs) pn ->
    path_eval_root fs pn (DirNode dirnum0) ->
    path_eval_root (create_file dirnum0 h name fs) pn (DirNode dirnum) ->
    dirnum = dirnum0.
Proof.
  intros.
  assert (DirNode dirnum = DirNode dirnum0) as Hinum.
  eapply path_eval_root_create in H4 as Hx; try eassumption.
  eapply path_unique_eq in H3; try eassumption.
  inversion Hinum; auto.
Qed.

Lemma path_evaluates_add_link_upd_file : forall fs startdir node h data dirpn from to name,
    path_evaluates (add_link from to name fs) startdir dirpn node ->
    path_evaluates (add_link from to name (upd_file h data fs)) startdir dirpn node.
Proof.
  intros.
  remember (add_link from to name fs).
  generalize dependent fs; intros.
  induction H.
  + constructor.
  + eapply PathEvalFileLink; eauto.
    inversion H; subst; clear H.
    - constructor; simpl; auto.
  + eapply PathEvalDirLink; eauto.
    inversion H; subst; clear H.
    - constructor; simpl; auto.
    - apply ValidDot.
    - eapply ValidDotDot; simpl; eauto.
    - apply ValidDotDotRoot; auto.
  + eapply PathEvalSymlink; subst; simpl.
    inversion H; subst; clear H.
    constructor; simpl; eauto.
    apply IHpath_evaluates1; eauto.
    apply IHpath_evaluates2; eauto.
Qed.

Lemma path_evaluates_add_link_upd_file' : forall fs startdir node h data dirpn from to name,
    path_evaluates (add_link from to name (upd_file h data fs)) startdir dirpn node ->
    path_evaluates (add_link from to name fs) startdir dirpn node.
Proof.
  intros.
  remember (add_link from to name (upd_file h data fs)).
  generalize dependent fs; intros.
  induction H.
  + constructor.
  + eapply PathEvalFileLink; eauto.
    inversion H; subst; clear H.
    - constructor; simpl; auto.
  + eapply PathEvalDirLink; eauto.
    inversion H; subst; clear H.
    - constructor; simpl; auto.
    - apply ValidDot.
    - eapply ValidDotDot; simpl; eauto.
    - apply ValidDotDotRoot; auto.
  + eapply PathEvalSymlink; subst; simpl.
    inversion H; subst; clear H.
    constructor; simpl; eauto.
    apply IHpath_evaluates1; eauto.
    apply IHpath_evaluates2; eauto.
Qed.

Lemma path_evaluates_add_link_comm: forall fs pn startdir dirnum0 name2 n1 name1 n2 node,
    path_evaluates (add_link dirnum0 n1 name1 (add_link dirnum0 n2 name2 fs)) (DirNode startdir) pn node ->
    path_evaluates (add_link dirnum0 n2 name2 (add_link dirnum0 n1 name1 fs)) (DirNode startdir) pn node.
Proof.
  intros.
  remember ((add_link dirnum0 n1 name1 (add_link dirnum0 n2 name2 fs))).
  generalize dependent fs; intros.
  induction H; subst.
  + constructor.
  + apply PathEvalFileLink; subst.
    inversion H; subst; clear H.
    constructor; simpl in *.
    apply In_add_add_comm; auto.
  + eapply PathEvalDirLink; eauto.
    inversion H; subst; clear H.
    - constructor; auto.
      apply In_add_add_comm; auto.
    - apply ValidDot.
    - eapply ValidDotDot.
      apply In_add_add_comm; eauto.
    - apply ValidDotDotRoot; auto.
  + inversion H; subst.
    eapply PathEvalSymlink; simpl.
    - constructor; simpl in *.
      apply In_add_add_comm; auto.
      apply H2.
    - apply IHpath_evaluates1; eauto.
    - apply IHpath_evaluates2; eauto.
Qed.

Lemma path_evaluates_add_link_add_link_upd_file: forall fs startdir dirnum0 node node0 node1 name0 name1 h data pn,
   path_evaluates
        (add_link dirnum0 node0 name0 (add_link dirnum0 node1 name1 (upd_file h data fs))) startdir pn node ->
   path_evaluates
     (add_link dirnum0 node0 name0 (add_link dirnum0 node1 name1 fs)) startdir pn node.
Proof.
  intros.
  remember (add_link dirnum0 node0 name0 (add_link dirnum0 node1 name1 (upd_file h data fs))).
  generalize dependent fs; intros.
  induction H; subst.
  + constructor.
  + eapply PathEvalFileLink; eauto.
    inversion H; subst; clear H.
    - constructor; simpl; auto.
  + eapply PathEvalDirLink; eauto.
    inversion H; subst; clear H.
    - constructor; simpl; auto.
    - apply ValidDot.
    - eapply ValidDotDot; simpl; eauto.
    - apply ValidDotDotRoot; auto.
  + eapply PathEvalSymlink; subst; simpl.
    inversion H; subst; clear H.
    constructor; simpl; eauto.
    apply IHpath_evaluates1; eauto.
    apply IHpath_evaluates2; eauto.
Qed.

Lemma path_evaluates_add_link_add_link_upd_file': forall fs startdir dirnum0 node node0 node1 name0 name1 h data pn,
   path_evaluates
     (add_link dirnum0 node0 name0 (add_link dirnum0 node1 name1 fs)) startdir pn node ->
   path_evaluates
        (add_link dirnum0 node0 name0 (add_link dirnum0 node1 name1 (upd_file h data fs))) startdir pn node.
Proof.
  intros.
  remember (add_link dirnum0 node0 name0 (add_link dirnum0 node1 name1 fs)).
  generalize dependent fs; intros.
  induction H; subst.
  + constructor.
  + eapply PathEvalFileLink; eauto.
    inversion H; subst; clear H.
    - constructor; simpl; auto.
  + eapply PathEvalDirLink; eauto.
    inversion H; subst; clear H.
    - constructor; simpl; auto.
    - apply ValidDot.
    - eapply ValidDotDot; simpl; eauto.
    - apply ValidDotDotRoot; auto.
  + eapply PathEvalSymlink; subst; simpl.
    inversion H; subst; clear H.
    constructor; simpl; eauto.
    apply IHpath_evaluates1; eauto.
    apply IHpath_evaluates2; eauto.
Qed.

Lemma path_evaluates_create_comm: forall fs pn startdir dirnum0 name0 v0 name1 v1 node,
    path_evaluates (create_file dirnum0 v0 name0 (create_file dirnum0 v1 name1 fs)) (DirNode startdir) pn node ->
    path_evaluates (create_file dirnum0 v1 name1 (create_file dirnum0 v0 name0 fs)) (DirNode startdir) pn node.
Proof.
  intros.
  unfold create_file in *.
  simpl in *.
  eapply path_evaluates_add_link_upd_file.
  eapply path_evaluates_add_link_upd_file' in H.
  eapply path_evaluates_add_link_add_link_upd_file in H.
  eapply path_evaluates_add_link_add_link_upd_file'.
  apply path_evaluates_add_link_comm; auto.
Qed.

Lemma path_eval_root_create_comm: forall fs pn dirnum0 name v0 name0 v1 node,
    path_eval_root (create_file dirnum0 v1 name0 (create_file dirnum0 v0 name fs)) pn node ->
    path_eval_root (create_file dirnum0 v0 name (create_file dirnum0 v1 name0 fs)) pn node.
Proof.
  intros.
  unfold path_eval_root in *.
  eapply path_evaluates_create_comm; eauto.
Qed.

Lemma unique_pathname_create_comm: forall fs pn dirnum0 name v0 name0 v1,
    unique_pathname_root (create_file dirnum0 v1 name0 (create_file dirnum0 v0 name fs)) pn ->
    unique_pathname_root (create_file dirnum0 v0 name (create_file dirnum0 v1 name0 fs)) pn.
Proof.
  intros.
  unfold unique_pathname_root in H.
  unfold unique_pathname_root.
  deex.
  exists node.
  split; auto.
  eapply path_evaluates_create_comm; try eassumption.
  intros.
  specialize (H0 node'); auto.
  edestruct H0.
  eapply path_evaluates_create_comm; try eassumption.
  reflexivity.
Qed.  

Lemma invariant_create_comm: forall fs dirnum0 name v0 name0 v1,
    invariant (create_file dirnum0 v1 name0 (create_file dirnum0 v0 name fs)) ->
    invariant (create_file dirnum0 v0 name (create_file dirnum0 v1 name0 fs)).
Proof.
  intros.
  unfold invariant in *.
  eapply unique_pathname_create_comm; eauto.
Qed.

Lemma unique_pathname_create: forall fs pn dirnum name1 v1,
    unique_pathname_root fs pn ->
    path_eval_root fs pn (DirNode dirnum) ->
    unique_pathname_root (create_file dirnum v1 name1 fs) pn.
Proof.
  intros.
  unfold unique_pathname_root, unique_pathname in *.
  repeat deex.
  unfold create_file, path_eval_root in *.
  eexists.
  split.
  eapply path_evaluates_add_link_upd_file; simpl.
  eapply path_evaluates_add_link in H as Hx.
  apply Hx.

  intros.
  eapply H1.
  eapply path_evaluates_add_link_upd_file' in H2.
  simpl in *.
  apply path_evaluates_add_link' in H2; simpl in *; eauto.
  unfold unique_pathname.
  eexists.
  split; eauto.
  intros.
  specialize (H1 node'0 H3) as H1x; subst.
  symmetry.
  specialize (H1 (DirNode dirnum) H0) as H1x; subst; auto.
Admitted.

Lemma invariant_create: forall fs dirnum name1 v1,
    path_eval_root fs tmpdir (DirNode dirnum) ->
    invariant fs ->
    invariant (create_file dirnum v1 name1 fs).
Proof.
  intros.
  unfold invariant in *.
  eapply unique_pathname_create; eauto.
Qed.

Lemma fsequiv_create_file_comm: forall fs dirnum h0 h1 name1 name0,
    file_handle_unused fs h0 ->
    file_handle_unused (create_file dirnum h0 name0 fs) h1 ->
    FSEquiv (create_file dirnum h1 name1 (create_file dirnum h0 name0 fs))
            (create_file dirnum h0 name0 (create_file dirnum h1 name1 fs)).
Proof.
  intros.
  unfold create_file, FSEquiv; simpl.
  destruct fs; simpl.
  intuition eauto.
  eapply list_upd_commutes.
  eapply file_handle_unused_ne in H0 as Hx; eauto.
  unfold Graph.Equal; split; intros.
  eapply In_add_add_comm; eauto.
  eapply In_add_add_comm; eauto.
Qed.

Theorem create_tmpdir_both_mover : forall dir name,
  both_mover mailfs_step (Create dir name).
Proof.
  split; intros.
  - unfold right_mover; intros.
    repeat step_inv; unfold mailfs_step; intuition eauto; simpl in *.
    repeat step_inv.
    repeat subst_fsequiv.

    replace dirnum with dirnum0 in *.
    2: eapply path_unique_create_inum_eq in H7 as Hi; auto.

    eexists; split; subst_fsequiv.
    + intuition idtac.
      econstructor; eauto.
      2: reflexivity; eauto.
      econstructor; eauto.
      eauto.

      eapply invariant_create; eauto.
      
      (* eapply invariant_create_comm in H11 as H11x; eauto. *)
        
      (* some come from econstructor; others form invariant_create *)
      Unshelve.
      all: auto.

    + intuition idtac.
      econstructor.
      econstructor.

      eapply path_eval_root_create in H8 as H8x.
      apply H8x.

      eauto.
      all: try unfold create_file; eauto.

      apply fsequiv_create_file_comm; auto.
      eapply invariant_create_comm in H11 as H11x; eauto.
      eapply invariant_create; eauto.
      Unshelve.
      all: auto.

  - admit.
Admitted.

*)
