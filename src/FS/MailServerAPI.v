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
  fs_invariant fs /\
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
  - rewrite H in H0; eexists; intuition eauto.
    eapply H2. rewrite H. eauto.
  - rewrite H in *.
    eauto.
  - rewrite <- H in H0; eexists; intuition eauto.
    eapply H2. rewrite <- H. eauto.
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

Lemma path_eval_root_create': forall fs pn dirnum h name node',
    name <> "." ->
    name <> ".." ->
    fs_invariant fs ->
    does_not_exist fs dirnum name ->
    file_handle_unused fs h ->
    file_handle_valid fs h ->
    path_eval_root fs pn (DirNode dirnum) ->
    path_eval_root (create_file dirnum h name fs) pn node' ->
    node' = (DirNode dirnum).
Proof.
  intros.
  eapply path_eval_root_addlink' in H6 as H6x; eauto.
  eapply path_eval_root_updfile' in H6x.
  eapply path_eval_root_eq; eauto.

  unfold fs_invariant, unique_dirents; intros.
  apply valid_link_updfile' in H7.
  apply valid_link_updfile' in H8.
  eapply H1; eauto.
  eapply path_eval_root_updfile; eauto.
Qed.

Lemma invariant_create : forall dirnum h name fs,
    name <> "." ->
    name <> ".." ->
    does_not_exist fs dirnum name ->
    file_handle_unused fs h ->
    file_handle_valid fs h ->
    path_eval_root fs tmpdir (DirNode dirnum) ->
    invariant fs ->
    invariant (create_file dirnum h name fs).
Proof.
  unfold invariant; intuition idtac.
  eapply fs_invariant_create; eauto.
  unfold unique_pathname in *; repeat deex.
  exists (DirNode dirnum); split.
  eapply path_eval_root_create in H4; eauto.
  intros.
  eapply path_eval_root_create'; eauto.
Qed.

Lemma path_unique_create_inum_eq: forall fs pn dirnum dirnum0 h name,
    invariant fs ->
    does_not_exist fs dirnum0 name ->
    file_handle_unused fs h ->
    file_handle_valid fs h ->
    invariant (create_file dirnum0 h name fs) ->
    path_eval_root fs pn (DirNode dirnum0) ->
    path_eval_root (create_file dirnum0 h name fs) pn (DirNode dirnum) ->
    dirnum = dirnum0.
Proof.
  intros.
  assert (DirNode dirnum = DirNode dirnum0) as Hinum.
  destruct H; intuition idtac.
  eapply path_eval_root_updfile in H4 as Hx.
  eapply path_eval_root_addlink in Hx.
  2: apply does_not_exist_updfile'; eauto.
  eapply path_eval_root_eq.
  3: apply Hx.
  2: eauto.
  unfold invariant in *; intuition idtac.
  inversion Hinum; auto.
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
      eapply invariant_create; eauto.

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
      eapply invariant_create; eauto.

      Unshelve.
      all: auto.

  - admit.
Admitted.
