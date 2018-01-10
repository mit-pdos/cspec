Require Import POCS.
Require Import Relations.Relation_Operators.
Require Import RelationClasses.
Require Import Morphisms.

Import ListNotations.
Require Import String.
Require Import Trees.

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
  eapply path_eval_root_updfile in H4 as Hx.
  eapply path_eval_root_addlink in Hx.
  apply Hx.
  eapply does_not_exist_updfile'; eauto.

  intros.

  eapply path_eval_root_addlink' in H8 as H8x; eauto.
  
  eapply path_eval_root_updfile' in H8x.
  eapply path_eval_root_eq; eauto.

  unfold fs_invariant, unique_dirents; intros.
  apply valid_link_updfile' in H9.
  apply valid_link_updfile' in H10.
  eapply H6; eauto.

  eapply path_eval_root_updfile; eauto.
Qed.


Theorem create_tmpdir_both_mover : forall dir name,
  both_mover mailfs_step (Create dir name).
Proof.
  split; intros.
  - unfold right_mover; intros.
    repeat step_inv; unfold mailfs_step; intuition eauto; simpl in *.
    repeat step_inv.
    repeat subst_fsequiv.

    (* Use the fact that tmpdir is unique to show that dirnum=dirnum0 *)
    assert (DirNode dirnum = DirNode dirnum0) as Hy.
    destruct H18; intuition idtac.
    eapply path_eval_root_updfile in H8 as Hx.
    eapply path_eval_root_addlink in Hx.
    2: apply does_not_exist_updfile'; eauto.
    eapply path_eval_root_eq.
    3: apply Hx.
    2: eauto.
    eapply fs_invariant_create; eauto.
    unfold invariant in *; intuition idtac.
    inversion Hy; clear Hy; subst.

    eexists; split; subst_fsequiv.
    + intuition idtac.

      econstructor.
      2: reflexivity.

      econstructor; eauto.
      eauto.

      eapply invariant_create; eauto.

    + intuition idtac.

      econstructor.

      econstructor.

      eapply path_eval_root_updfile in H8 as H8x.
      eapply path_eval_root_addlink in H8x.
      apply H8x.

      eauto.
      unfold create_file; eauto.
      unfold create_file; eauto.
      unfold create_file; eauto.
      unfold create_file; eauto.
      unfold create_file; eauto.

      {
        destruct s.
        unfold add_link, upd_file.
        unfold FSEquiv.
        simpl.
        intuition eauto.
        eapply list_upd_commutes.
        eapply file_handle_unused_ne in H13 as Hx; eauto.


        unfold Graph.Equal; split; intros.
        {
          eapply Graph.add_spec in H0; intuition idtac; subst.
          eapply Graph.add_spec; right. eapply Graph.add_spec; eauto.
          eapply Graph.add_spec in H3; intuition idtac; subst.
          eapply Graph.add_spec; eauto.
          eapply Graph.add_spec; right. eapply Graph.add_spec; eauto.
        }
        {
          eapply Graph.add_spec in H0; intuition idtac; subst.
          eapply Graph.add_spec; right. eapply Graph.add_spec; eauto.
          eapply Graph.add_spec in H3; intuition idtac; subst.
          eapply Graph.add_spec; eauto.
          eapply Graph.add_spec; right. eapply Graph.add_spec; eauto.
        }
      }

      eauto.

      eapply invariant_create; eauto.

  - admit.
Admitted.
