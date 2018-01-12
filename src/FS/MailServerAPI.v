Require Import POCS.
Require Import Relations.Relation_Operators.
Require Import RelationClasses.
Require Import Morphisms.

Import ListNotations.
Require Import String.
Require Import FSAPI.

Definition maildir := ["/tmp/"%string; "mail/"%string].
Definition tmpdir := ["/tmp/"%string].

Global Opaque maildir.
Global Opaque tmpdir.

Parameter tid_to_string : nat -> string.

Definition starts_with_tid tid (name : string) : Prop :=
  exists namesuffix,
    name = (tid_to_string tid ++ "." ++ namesuffix)%string.

Axiom starts_with_tid_not_dot : forall tid name,
  starts_with_tid tid name -> name <> ".".
Axiom starts_with_tid_not_dotdot : forall tid name,
  starts_with_tid tid name -> name <> "..".

Hint Resolve starts_with_tid_not_dot.
Hint Resolve starts_with_tid_not_dotdot.

Inductive mailfs_step_allowed : forall T, fsOpT T -> nat -> Prop :=
| MailStepCreateTmp : forall dir name tid,
  dir = tmpdir ->
  starts_with_tid tid name ->
  mailfs_step_allowed (Create dir name) tid.

(*
| MailStepFindAvailableNameTmp : forall tid,
  mailfs_step_allowed (FindAvailableName tmpdir) tid

| MailStepFindAvailableNameUser : forall user dir tid,
  dir = (maildir ++ [user])%list ->
  mailfs_step_allowed (FindAvailableName dir) tid

| MailStepWriteTmp : forall pn dir name tid data,
  dir = tmpdir ->
  starts_with_tid tid name ->
  pn = (dir ++ [name])%list ->
  mailfs_step_allowed (Write pn data) tid

| MailStepRenameTmpToMailbox : forall src srcname dstdir user dstname tid,
  src = (tmpdir ++ [srcname])%list ->
  starts_with_tid tid srcname ->
  dstdir = (maildir ++ [user])%list ->
  starts_with_tid tid dstname ->
  mailfs_step_allowed (Rename src dstdir dstname) tid
.
*)

Definition invariant (fs : FS) :=
  unique_pathname fs tmpdir.

Definition mailfs_step T (op : fsOpT T) tid s r s' :=
  fs_step_equiv op tid s r s' /\
  mailfs_step_allowed op tid /\
  invariant s /\
  invariant s'.

Definition message := string.

Inductive mailT : Type -> Type :=
| Deliver (user : string) (m : message) : mailT unit.


Definition deliver_core (user : string) (m : message) : proc fsOpT mailT unit :=
  tmpname <- Op (FindAvailableName tmpdir);
  _ <- Op (Create tmpdir tmpname);
  _ <- Op (Write (tmpdir ++ [tmpname])%list m);
  fn <- Op (FindAvailableName (maildir ++ [user])%list);
  _ <- Op (Rename (tmpdir ++ [tmpname])%list (maildir ++ [user])%list fn);
  Ret tt.

Ltac step_inv :=
  match goal with
  | H : fs_step _ _ _ _ _ |- _ =>
    inversion H; clear H; subst; repeat sigT_eq
  | H : fs_step_equiv _ _ _ _ _ |- _ =>
    inversion H; clear H; subst; repeat sigT_eq
  | H : mailfs_step _ _ _ _ _ |- _ =>
    inversion H; clear H; subst; repeat sigT_eq
  | H : mailfs_step_allowed _ _ |- _ =>
    inversion H; clear H; subst; repeat sigT_eq
  end.

Hint Constructors mailfs_step_allowed.

Axiom tmpdir_not_maildir : forall user, tmpdir = (maildir ++ [user])%list -> False.
Hint Resolve tmpdir_not_maildir.

Axiom starts_with_tid_ne : forall tid0 tid1 name0 name1,
  tid0 <> tid1 ->
  starts_with_tid tid0 name0 ->
  starts_with_tid tid1 name1 ->
  name0 <> name1.

Hint Resolve starts_with_tid_ne.

Instance invariant_proper :
  Proper (FSEquiv ==> iff) invariant.
Proof.
  intros ? ? ?; subst.
  unfold invariant, unique_pathname; intuition; repeat deex.
  - rewrite <- H in *.
    eauto.
  - specialize (H0 node node').
    rewrite H in H1.
    rewrite H in H2.
    specialize (H0 H1 H2); auto.
Qed.

Lemma path_eval_root_create: forall fs pn dirnum h name,
    does_not_exist fs dirnum name ->
    path_eval_root fs pn (DirNode dirnum) ->
    path_eval_root (create_file dirnum h name fs) pn (DirNode dirnum ).
Proof.
  intros.
  eapply path_eval_root_updfile in H0.
  eapply path_eval_root_addlink in H0; eauto.
Qed.

Lemma valid_link_addlink_does_not_exists: forall fs dirnum name h node' node'' startdir name0,
    name <> "." ->
    name <> ".." ->
    does_not_exist fs dirnum name ->
    valid_link fs startdir name0 node'' ->
    valid_link (add_link dirnum (FileNode h) name fs) startdir name0 node' ->
    valid_link fs startdir name0 node'.
Proof.
  intros.
  inversion H3; subst.
  apply Graph.add_spec in H4.
  intuition; subst. 
  inversion H5; subst. clear H5.
  destruct H1.
  eexists.
  inversion H2; subst; eauto; try congruence.
  apply ValidDot.
  eapply ValidDotDot.
  apply Graph.add_spec in H4.
  intuition; subst; try congruence.
  eauto.
  eapply ValidDotDotRoot.
  unfold add_link; simpl; auto.
Qed.

Lemma path_eval_addlink' : forall fs dirpn startdir dirnum h name node,
    name <> "." ->
    name <> ".." ->
     (forall node node' : Node,
       path_evaluates fs (DirNode startdir) dirpn node ->
       path_evaluates fs (DirNode startdir) dirpn node' -> node' = node) ->
    does_not_exist fs dirnum name ->
    path_evaluates fs (DirNode startdir) dirpn (DirNode dirnum) ->
    path_evaluates (add_link dirnum (FileNode h) name fs) (DirNode startdir) dirpn node ->
    DirNode dirnum = node.
Proof.
  intros.
  generalize dependent fs; intros.
  induction H3.
  + inversion H4; subst; auto.
  + inversion H4; subst; clear H4.
    eapply valid_link_addlink_does_not_exists in H8; eauto.
    inversion H11; subst.
    eapply valid_link_addlink_does_not_exists in H9; eauto.
    inversion H12; subst; clear H12.
    eapply valid_link_addlink_does_not_exists in H9; eauto.
    exfalso. admit.
  + inversion H4; subst; clear H4.
    eapply valid_link_addlink_does_not_exists in H11; eauto.
    {
      eapply valid_link_addlink_does_not_exists in H10; eauto.
      assert (inum = inum0).
      admit.
      subst.
      apply IHpath_evaluates; try eassumption.
      admit.
    }
    { 
      eapply valid_link_addlink_does_not_exists in H10; eauto.
      admit.  (* H10 and H3 and H1 *)
    }
  + inversion H4; subst. clear H4.
    eapply valid_link_addlink_does_not_exists in H10; eauto.
    {
      eapply valid_link_addlink_does_not_exists in H9; eauto.
      admit.  (* H9 and H3 and H1 *)
    }
    eapply valid_link_addlink_does_not_exists in H9; eauto.
    assert (sympath0 = sympath).
    admit.
    subst.
    assert (symtarget = node).
    subst.
    eapply IHpath_evaluates1.
    admit.
    auto.
    assert (node = symtarget0).
    admit.
    subst.
    auto.
    apply IHpath_evaluates2; auto.
    admit.
    assert (symtarget0 = symtarget).
    admit.
    subst.
    auto.
 Admitted.

Lemma path_eval_root_addlink' : forall fs dirnum name dirpn h node,
    name <> "." ->
    name <> ".." ->
    does_not_exist fs dirnum name ->
    unique_pathname fs dirpn ->
    path_eval_root fs dirpn (DirNode dirnum) ->
    path_eval_root (add_link dirnum (FileNode h) name fs) dirpn node ->
    DirNode dirnum = node.
Proof.
  unfold unique_pathname, path_eval_root.
  intros.
  eapply path_eval_addlink'; try eassumption.
Qed.

Lemma path_eval_root_create': forall fs pn node dirnum h name,
    name <> "." ->
    name <> ".." ->
    does_not_exist fs dirnum name ->
    unique_pathname fs pn ->
    path_eval_root fs pn (DirNode dirnum) ->
    path_eval_root (create_file dirnum h name fs) pn node ->
    DirNode dirnum = node.
Proof.
  intros.
  unfold create_file in *.
  eapply path_eval_root_updfile with (h := h) (data := "") in H3.
  eapply path_eval_root_addlink' with (fs := (upd_file h "" fs)); try eassumption.
  unfold upd_file; simpl.
  admit.
Admitted.

Lemma path_unique_eq: forall fs dirnum pn node',
    unique_pathname fs pn ->
    path_eval_root fs pn (DirNode dirnum) ->
    path_eval_root fs pn node' ->
    node' = DirNode dirnum.
Proof.
  intros.
  unfold unique_pathname in *.
  specialize (H (DirNode dirnum) node').
  specialize (H H0 H1).
  auto.
Qed.

Lemma path_unique_create_inum_eq: forall fs pn dirnum dirnum0 h name,
    unique_pathname fs pn ->
    does_not_exist fs dirnum0 name ->
    file_handle_unused fs h ->
    file_handle_valid fs h ->
    unique_pathname (create_file dirnum0 h name fs) pn ->
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

Lemma invariant_create : forall fs pn dirnum h name,
    name <> "." ->
    name <> ".." ->
    unique_pathname fs pn ->
    does_not_exist fs dirnum name ->
    file_handle_unused fs h ->
    file_handle_valid fs h ->
    path_eval_root fs pn (DirNode dirnum) ->
    unique_pathname (create_file dirnum h name fs) pn.
Proof.
  intros.
  unfold unique_pathname.
  intros.
  assert (DirNode dirnum = node).
  eapply path_eval_root_create' in H6; try eassumption.
  subst.
  symmetry.
  eapply path_eval_root_create' in H7; try eassumption.
Qed.

Lemma create_file_comm: forall fs dirnum h0 h1 name1 name0,
    file_handle_unused fs h0 ->
    file_handle_unused (create_file dirnum h0 name0 fs) h1 ->
    FSEquiv (create_file dirnum h1 name1 (create_file dirnum h0 name0 fs))
            (create_file dirnum h0 name0 (create_file dirnum h1 name1 fs)).
Proof.
  intros.
  unfold create_file, add_link, upd_file, FSEquiv; simpl.
  destruct fs; simpl.
  intuition eauto.
  eapply list_upd_commutes.
  eapply file_handle_unused_ne in H0 as Hx; eauto.
  unfold Graph.Equal; split; intros.
  {
    eapply Graph.add_spec in H1; intuition idtac; subst.
    eapply Graph.add_spec; right. eapply Graph.add_spec; eauto.
    eapply Graph.add_spec in H2; intuition idtac; subst.
    eapply Graph.add_spec; eauto.
    eapply Graph.add_spec; right. eapply Graph.add_spec; eauto.
  }
  {
    eapply Graph.add_spec in H1; intuition idtac; subst.
    eapply Graph.add_spec; right. eapply Graph.add_spec; eauto.
    eapply Graph.add_spec in H2; intuition idtac; subst.
    eapply Graph.add_spec; eauto.
    eapply Graph.add_spec; right. eapply Graph.add_spec; eauto.
  }
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

      apply invariant_create; try eauto.
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

      apply create_file_comm; auto.
      apply invariant_create; try eauto.
      Unshelve.
      all: auto.

  - admit.
Admitted.
