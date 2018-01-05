Require Import POCS.
Require Import Relations.Relation_Operators.
Require Import RelationClasses.
Require Import Morphisms.


Import ListNotations.
Require Import String.
Require Import Trees.


Definition State := FS.

Definition maildir := ["/tmp/"%string; "mail/"%string].
Definition tmpdir := ["/tmp/"%string].

Global Opaque maildir.
Global Opaque tmpdir.


Inductive stat_result :=
| StatMissing
| StatFile
| StatDir.

Inductive fsOpT : Type -> Type :=
| Create (dir : Pathname) (name : string) : fsOpT nat
| Mkdir (dir : Pathname) (name : string) : fsOpT nat
| Delete (pn : Pathname) : fsOpT unit
| Rmdir (pn : Pathname) : fsOpT unit
| Stat (dir : Pathname) (name : string) : fsOpT stat_result
| Readdir (pn : Pathname) : fsOpT (list string)
| Rename (src : Pathname) (dstdir : Pathname) (dstname : string) : fsOpT unit
| Read (pn : Pathname) : fsOpT string
| Write (pn : Pathname) (data : string) : fsOpT unit
| FindAvailableName (dir : Pathname) : fsOpT string
| Debug (s : string) : fsOpT unit.


Parameter tid_to_string : nat -> string.

Definition starts_with_tid tid (name : string) : Prop :=
  exists namesuffix,
    name = (tid_to_string tid ++ "." ++ namesuffix)%string.


Section StepXform.

  Variable opT : Type -> Type.
  Variable op_step : OpSemantics opT State.
  Variable EquivR : Relation_Definitions.relation State.

  Inductive equiv_step : OpSemantics opT State :=
  | StepEquiv : forall `(op : opT T) tid s0 s1 s1' r,
    op_step op tid s0 r s1' ->
    EquivR s1 s1' ->
    equiv_step op tid s0 r s1.

End StepXform.


(* These mutators should go into Trees.v *)

Definition does_not_exist (fs : FS) dirnum name :=
  ~ exists n, Graph.In (mkLink dirnum n name) (FSLinks fs).

Definition file_handle_unused (fs : FS) h :=
  ~ exists d name, Graph.In (mkLink d (FileNode h) name) (FSLinks fs).

Definition file_handle_valid (fs : FS) h :=
  h < Datatypes.length (FSFiles fs).

Definition upd_file h data (fs : FS) :=
  mkFS (FSRoot fs) (FSLinks fs) (list_upd (FSFiles fs) h data).

Definition add_link dir node name (fs : FS) :=
  mkFS (FSRoot fs) (Graph.add (mkLink dir node name) (FSLinks fs)) (FSFiles fs).

Definition valid_dir dir (fs : FS) :=
  exists pn, path_eval_root fs pn (DirNode dir).


Inductive fs_step : forall T, fsOpT T -> nat -> State -> T -> State -> Prop :=
| StepCreateAt : forall dir dirnum name tid s h s',
  path_eval_root s dir (DirNode dirnum) ->
  does_not_exist s dirnum name ->
  file_handle_unused s h ->
  file_handle_valid s h ->
  s' = add_link dirnum (FileNode h) name (upd_file h "" s) ->
  fs_step (Create dir name) tid s h s'

(*

| StepMkdir : forall dir name tid s h s' dirnum newdirnum,
  frame_pre_post s s'
    (dir |-> Dir dirnum * (dir ++ [name]) |-> Missing)
    (dir |-> Dir dirnum * (dir ++ [name]) |-> Dir newdirnum
                        * subtree_pred (dir ++ [name]) empty_dir) ->
  fs_step (Mkdir dir name) tid s h s'

| StepDelete : forall pn h f tid s s',
  frame_pre_post s s'
    (pn |-> File h f)
    (pn |-> Missing) ->
  fs_step (Delete pn) tid s tt s'

| StepRmdir : forall pn dirnum tid s s',
  frame_pre_post s s'
    (pn |-> Dir dirnum * subtree_pred pn empty_dir)
    (pn |-> Missing) ->
  fs_step (Rmdir pn) tid s tt s'

| StepStat : forall dir name tid s r F dirnum,
  s  |= F * dir |-> Dir dirnum ->
  (r = StatFile ->
    exists F' h f, F' * (dir ++ [name]) |-> File h f ===> F) ->
  (r = StatDir ->
    exists F' dirnum', F' * (dir ++ [name]) |-> Dir dirnum' ===> F) ->
  (r = StatMissing ->
    exists F', F' * (dir ++ [name]) |-> Missing ===> F) ->
  fs_step (Stat dir name) tid s r s

| StepReaddir : forall dir tid s r F dirnum,
  s  |= F * dir |-> Dir dirnum ->
  (forall fn,
    (In fn r /\ exists F' handle f,
     F' * (dir ++ [fn]) |-> File handle f ===> F) \/
    (In fn r /\ exists F' dirinum,
     F' * (dir ++ [fn]) |-> Dir dirinum ===> F) \/
    (~ In fn r /\ exists F',
     F' * (dir ++ [fn]) |-> Missing ===> F)) ->
  fs_step (Readdir dir) tid s r s

| StepRename : forall src dstdir dstname tid s handle f s' dirnum,
  frame_pre_post s s'
    (src |-> File handle f
          * dstdir |-> Dir dirnum
          * (dstdir ++ [dstname]) |-> Missing)
    (src |-> Missing
          * dstdir |-> Dir dirnum
          * (dstdir ++ [dstname]) |-> File handle f) ->
  fs_step (Rename src dstdir dstname) tid s tt s'

| StepRead : forall pn tid s r handle F,
  s  |= F * pn |-> File handle r ->
  fs_step (Read pn) tid s (FileData r) s

| StepWrite : forall pn tid s s' handle f0 data,
  frame_pre_post s s'
    (pn |-> File handle f0)
    (pn |-> File handle (mk_file data)) ->
  fs_step (Write pn data) tid s tt s'

| StepFindAvailableName : forall dir dirnum tid s name F,
  starts_with_tid tid name ->
  s  |= F * dir |-> Dir dirnum * (dir ++ [name]) |-> Missing ->
  fs_step (FindAvailableName dir) tid s name s

| StepDebug : forall msg tid s,
  fs_step (Debug msg) tid s tt s
*)
.


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

Definition fs_step_equiv : OpSemantics fsOpT State :=
  equiv_step fs_step FSEquiv.

Definition unique_pathname (fs : FS) pn :=
  exists node,
    path_eval_root fs pn node /\
    forall node',
      path_eval_root fs pn node' -> node' = node.

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

Hint Constructors fs_step.
Hint Constructors mailfs_step_allowed.

Axiom tmpdir_not_maildir : forall user, tmpdir = (maildir ++ [user])%list -> False.
Hint Resolve tmpdir_not_maildir.

Axiom starts_with_tid_ne : forall tid0 tid1 name0 name1,
  tid0 <> tid1 ->
  starts_with_tid tid0 name0 ->
  starts_with_tid tid1 name1 ->
  name0 <> name1.

Hint Resolve starts_with_tid_ne.


Instance fs_step_equiv_proper :
  Proper (eq ==> eq ==> eq ==> eq ==> FSEquiv ==> iff) (@fs_step_equiv T).
Proof.
  intros.
  intros ? ? ?; subst.
  intros ? ? ?; subst.
  intros fs1 fs1' ?.
  intros ? ? ?; subst.
  intros fs2 fs2' ?.
  unfold fs_step_equiv; intuition.
  - inversion H0; clear H0; repeat sigT_eq.
    econstructor; eauto.
    etransitivity; eauto.
      symmetry; eauto.
  - inversion H0; clear H0; repeat sigT_eq.
    econstructor; eauto.
    etransitivity; eauto.
Qed.

Instance file_handle_unused_proper :
  Proper (FSEquiv ==> eq ==> iff) file_handle_unused.
Proof.
  intros ? ? ?; subst.
  intros ? ? ?; subst.
  unfold FSEquiv in H.
  unfold file_handle_unused; intuition; repeat deex.
  - apply H2 in H3. eauto.
  - apply H2 in H3. eauto.
Qed.

Instance file_handle_valid_proper :
  Proper (FSEquiv ==> eq ==> iff) file_handle_valid.
Proof.
  intros ? ? ?; subst.
  intros ? ? ?; subst.
  unfold FSEquiv in H.
  unfold file_handle_valid; intuition; congruence.
Qed.

Instance does_not_exist_proper :
  Proper (FSEquiv ==> eq ==> eq ==> iff) does_not_exist.
Proof.
  intros ? ? ?; subst.
  intros ? ? ?; subst.
  intros ? ? ?; subst.
  unfold FSEquiv in H.
  unfold does_not_exist; intuition; repeat deex.
  - apply H2 in H3. eauto.
  - apply H2 in H3. eauto.
Qed.

Instance FSEquiv_proper :
  Proper (FSEquiv ==> FSEquiv ==> iff) FSEquiv.
Proof.
  intros ? ? ?; subst.
  intros ? ? ?; subst.
  rewrite H. rewrite H0. reflexivity.
Qed.

Instance upd_file_proper :
  Proper (eq ==> eq ==> FSEquiv ==> FSEquiv) upd_file.
Proof.
  intros ? ? ?; subst.
  intros ? ? ?; subst.
  intros ? ? ?; subst.
  unfold upd_file.
  unfold FSEquiv in *.
  intuition; simpl.
  rewrite H; eauto.
Qed.

Instance add_link_proper :
  Proper (eq ==> eq ==> eq ==> FSEquiv ==> FSEquiv) add_link.
Proof.
  intros ? ? ?; subst.
  intros ? ? ?; subst.
  intros ? ? ?; subst.
  intros ? ? ?; subst.
  unfold add_link.
  unfold FSEquiv in *.
  intuition; simpl.

  unfold Graph.Equal; split; intros; apply Graph.add_spec.
  - apply Graph.add_spec in H1; intuition; subst.
    apply H2 in H3. eauto.
  - apply Graph.add_spec in H1; intuition; subst.
    apply H2 in H3. eauto.
Qed.

Instance invariant_proper :
  Proper (FSEquiv ==> iff) invariant.
Proof.
  intros ? ? ?; subst.
  unfold invariant, unique_pathname; intuition; repeat deex.
  - rewrite H in H0; eexists; intuition eauto.
    eapply H1. rewrite H. eauto.
  - rewrite <- H in H0; eexists; intuition eauto.
    eapply H1. rewrite <- H. eauto.
Qed.


Lemma path_eval_root_addlink : forall fs dirnum name dirpn n,
  path_eval_root fs dirpn (DirNode dirnum) ->
  does_not_exist fs dirnum name ->
  path_eval_root (add_link dirnum n name fs) dirpn (DirNode dirnum).
Proof.
  unfold path_eval_root, add_link, does_not_exist in *.
  simpl in *.
  intros.
  induction H.
  + constructor.
  + eapply PathEvalLink; eauto.
    edestruct H.
    (* validlink constructors: *)
    - constructor; simpl.
      apply Graph.add_spec; auto.
    - apply ValidDot.
    - eapply ValidDotDot.
      apply Graph.add_spec; auto.
      right; eauto.
    - apply ValidDotDotRoot; auto.
  + eapply PathEvalSymlink; simpl.
    apply Graph.add_spec; right; eauto.
    apply IHpath_evaluates1; eauto.
    apply IHpath_evaluates2; eauto.
Qed.
    
Lemma path_eval_root_updfile : forall fs dirnum h data dirpn,
  path_eval_root fs dirpn (DirNode dirnum) ->
  path_eval_root (upd_file h data fs) dirpn (DirNode dirnum).
Proof.
  intros.
  unfold path_eval_root, upd_file; simpl.
  induction H.
  + constructor.
  + eapply PathEvalLink; eauto.
    edestruct H.
    - constructor; simpl; auto.
    - apply ValidDot.
    - eapply ValidDotDot; simpl; auto.
      apply H1.
    - apply ValidDotDotRoot; auto.
  + eapply PathEvalSymlink; simpl.
    apply H.
    apply IHpath_evaluates1; eauto.
    apply IHpath_evaluates2; eauto.
Qed.
    
Lemma does_not_exist_addlink : forall fs dirnum name dirnum0 n0 name0,
  does_not_exist (add_link dirnum0 n0 name0 fs) dirnum name ->
  does_not_exist fs dirnum name.
Proof.
  intros.
  unfold does_not_exist, add_link in *.
  simpl in *.
  intro.
  destruct H.
  deex.
  eexists.
  apply Graph.add_spec. right.
  apply H.
Qed.
  
Lemma does_not_exist_addlink_same_dirnum : forall fs dirnum name n0 name0,
  does_not_exist fs dirnum name ->
  name <> name0 ->
  does_not_exist (add_link dirnum n0 name0 fs) dirnum name.
Proof.
  intros.
  unfold does_not_exist, add_link in *.
  simpl in *.
  intro.
  deex.
  apply Graph.add_spec in H1.
  intuition idtac.
  inversion H2; congruence.
  destruct H.
  eexists.
  apply H2.
Qed.
  
Lemma does_not_exist_updfile : forall fs h data dirnum name,
  does_not_exist (upd_file h data fs) dirnum name ->
  does_not_exist fs dirnum name.
Proof.
  intros.
  unfold does_not_exist, upd_file in *.
  simpl in *; auto.
Qed.

Lemma does_not_exist_updfile' : forall fs h data dirnum name,
  does_not_exist fs dirnum name ->
  does_not_exist (upd_file h data fs) dirnum name.
Proof.
  intros.
  unfold does_not_exist, upd_file in *.
  simpl in *; auto.
Qed.
  
Hint Resolve does_not_exist_addlink.
Hint Resolve does_not_exist_addlink_same_dirnum.
Hint Resolve does_not_exist_updfile.
Hint Resolve does_not_exist_updfile'.

Lemma file_handle_unused_updfile : forall fs h0 data0 h,
  file_handle_unused (upd_file h0 data0 fs) h ->
  file_handle_unused fs h.
Proof.
  intros.
  unfold file_handle_unused, upd_file in *.
  simpl in *; auto.
Qed.

Lemma file_handle_unused_addlink : forall fs dirnum n name h,
  file_handle_unused (add_link dirnum n name fs) h ->
  file_handle_unused fs h.
Proof.
  intros.
  unfold file_handle_unused, add_link in *.
  simpl in *.
  intro.
  repeat deex.
  destruct H.
  repeat eexists.
  apply Graph.add_spec.
  right. apply H0.
Qed.
  
Lemma file_handle_unused_updfile' : forall fs h0 data0 h,
  file_handle_unused fs h ->
  file_handle_unused (upd_file h0 data0 fs) h.
Proof.
  intros.
  unfold file_handle_unused, upd_file in *.
  simpl in *; auto.
Qed.

Lemma file_handle_unused_addlink' : forall fs dirnum n name h,
  file_handle_unused fs h ->
  n <> FileNode h ->
  file_handle_unused (add_link dirnum n name fs) h.
Proof.
  intros.
  unfold file_handle_unused, add_link in *.
  simpl in *.
  intro.
  repeat deex.
  apply Graph.add_spec in H1.
  intuition idtac.
  inversion H2; congruence.
  destruct H.
  repeat eexists.
  apply H2.
Qed.
  
Lemma file_handle_unused_ne : forall fs dirnum v0 v1 name,
  file_handle_unused (add_link dirnum (FileNode v0) name fs) v1 ->
  FileNode v1 <> FileNode v0.
Proof.
  intros.
  unfold file_handle_unused, add_link in *.
  simpl in *.
  intro.
  destruct H.
  repeat eexists.
  apply Graph.add_spec.
  left. rewrite H0; eauto.
Qed.

Hint Resolve file_handle_unused_updfile.
Hint Resolve file_handle_unused_addlink.
Hint Resolve file_handle_unused_addlink'.
Hint Resolve file_handle_unused_ne.

Lemma file_handle_valid_updfile : forall fs h0 data0 h,
  file_handle_valid (upd_file h0 data0 fs) h ->
  file_handle_valid fs h.
Proof.
  intros.
  unfold file_handle_valid, file_handle_valid, upd_file in *.
  simpl in *.
  rewrite length_list_upd in H; auto.
Qed.

Lemma file_handle_valid_addlink : forall fs dirnum n name h,
  file_handle_valid (add_link dirnum n name fs) h ->
  file_handle_valid fs h.
Proof.
  intros.
  unfold file_handle_valid, file_handle_valid, add_link in *.
  simpl in *; auto.
Qed.

Lemma file_handle_valid_updfile' : forall fs h0 data0 h,
  file_handle_valid fs h ->
  file_handle_valid (upd_file h0 data0 fs) h.
Proof.
  intros.
  unfold file_handle_valid, file_handle_valid, upd_file in *.
  simpl in *.
  rewrite length_list_upd; auto.
Qed.
  
Lemma file_handle_valid_addlink' : forall fs dirnum n name h,
  file_handle_valid fs h ->
  file_handle_valid (add_link dirnum n name fs) h.
Proof.
  intros.
  unfold file_handle_valid, file_handle_valid, add_link in *.
  simpl in *; auto.
Qed.
  
Hint Resolve file_handle_valid_updfile.
Hint Resolve file_handle_valid_addlink.
Hint Resolve file_handle_valid_updfile'.
Hint Resolve file_handle_valid_addlink'.


Ltac subst_fsequiv :=
  match goal with
  | H : FSEquiv ?s1 ?s2 |- _ =>
    idtac "substituting" s1 "using" H; rewrite H in *; clear H; clear s1;
    idtac "cleared" s1
  | H : FSEquiv ?s1 ?s2 |- _ =>
    idtac "substituting" s2 "using" H; rewrite <- H in *; clear H; clear s2;
    idtac "cleared" s2
  end.

Theorem create_tmpdir_both_mover : forall dir name,
  both_mover mailfs_step (Create dir name).
Proof.
  split; intros.
  - unfold right_mover; intros.
    repeat step_inv; unfold mailfs_step; intuition eauto; simpl in *.
    repeat step_inv.
    repeat subst_fsequiv.

    (* Use the fact that tmpdir is unique to show that dirnum=dirnum0 *)
    destruct H18; intuition idtac.
    eapply path_eval_root_updfile in H8 as Hx.
    eapply path_eval_root_addlink in Hx.
    2: apply does_not_exist_updfile'; eauto.
    eapply H6 in H7 as H7'; subst.
    eapply H6 in Hx; inversion Hx; clear Hx; subst.

    eexists; split; subst_fsequiv.
    + intuition idtac.

      econstructor.
      2: reflexivity.

      econstructor; eauto.
      eauto.
      admit.

    + intuition idtac.

      econstructor.

      econstructor.

      admit.
      eauto.
      eauto.
      eauto.
      reflexivity.

      {
        destruct s.
        unfold add_link, upd_file.
        unfold FSEquiv.
        simpl.
        intuition eauto.
        admit.

        unfold Graph.Equal; split; intros.
        {
          eapply Graph.add_spec in H0; intuition idtac; subst.
          eapply Graph.add_spec; right. eapply Graph.add_spec; eauto.
          eapply Graph.add_spec in H9; intuition idtac; subst.
          eapply Graph.add_spec; eauto.
          eapply Graph.add_spec; right. eapply Graph.add_spec; eauto.
        }
        {
          eapply Graph.add_spec in H0; intuition idtac; subst.
          eapply Graph.add_spec; right. eapply Graph.add_spec; eauto.
          eapply Graph.add_spec in H9; intuition idtac; subst.
          eapply Graph.add_spec; eauto.
          eapply Graph.add_spec; right. eapply Graph.add_spec; eauto.
        }
      }

      eauto.
      admit.

  - admit.
Admitted.
