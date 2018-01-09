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

Axiom starts_with_tid_not_dot : forall tid name,
  starts_with_tid tid name -> name <> ".".
Axiom starts_with_tid_not_dotdot : forall tid name,
  starts_with_tid tid name -> name <> "..".

Hint Resolve starts_with_tid_not_dot.
Hint Resolve starts_with_tid_not_dotdot.


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

Definition create_file dir h name (fs : FS) :=
  add_link dir (FileNode h) name (upd_file h "" fs).

Definition valid_dir dir (fs : FS) :=
  exists pn, path_eval_root fs pn (DirNode dir).


Inductive fs_step : forall T, fsOpT T -> nat -> State -> T -> State -> Prop :=
| StepCreateAt : forall dir dirnum name tid s h s',
  path_eval_root s dir (DirNode dirnum) ->
  does_not_exist s dirnum name ->
  file_handle_unused s h ->
  file_handle_valid s h ->
  s' = create_file dirnum h name s ->
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

Definition unique_dirents (fs : FS) :=
  forall dir name target target0,
    valid_link fs dir name target ->
    valid_link fs dir name target0 ->
    target0 = target.

Definition fs_invariant (fs : FS) :=
  unique_dirents fs.

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

Instance create_file_proper :
  Proper (eq ==> eq ==> eq ==> FSEquiv ==> FSEquiv) create_file.
Proof.
  intros ? ? ?; subst.
  intros ? ? ?; subst.
  intros ? ? ?; subst.
  intros ? ? ?; subst.
  unfold create_file.
  rewrite H.
  reflexivity.
Qed.

Instance fs_invariant_proper :
  Proper (FSEquiv ==> iff) fs_invariant.
Proof.
  intros ? ? ?; subst.
  unfold fs_invariant, unique_dirents; intuition.
  - rewrite <- H in *.
    eauto.
  - rewrite H in *.
    eauto.
Qed.

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

Lemma valid_link_eq: forall fs dir a node node0,
    fs_invariant fs ->
    valid_link fs dir a node ->
    valid_link fs dir a node0 ->
    node = node0.
Proof.
  unfold fs_invariant, unique_dirents in *.
  intros; eauto.
Qed.

Lemma path_evaluates_eq: forall pn fs dir node node',
    fs_invariant fs ->
    path_evaluates fs dir pn node ->
    path_evaluates fs dir pn node'->
    node = node'.
Proof.
  intros.
  generalize dependent node'.
  induction H0; intros.
  + inversion H1; subst.
    inversion H1; subst; auto.
  + inversion H1; subst.
    eapply valid_link_eq in H0; eauto.
    exfalso.
    eapply valid_link_eq with (node := (DirNode inum0)) in H0; auto.
    inversion H0.
    exfalso.
    eapply valid_link_eq with (node := (SymlinkNode sympath)) in H0; auto.
    inversion H0.
  + inversion H2; subst.
    - exfalso.
      eapply valid_link_eq with (node := (FileNode inum0)) in H0; auto.
      inversion H0.
    - eapply valid_link_eq in H0; eauto.
      inversion H0; subst.
      apply IHpath_evaluates; auto.
    - exfalso.
      eapply valid_link_eq with (node := (SymlinkNode sympath)) in H0; auto.
      inversion H0.
  + inversion H1; subst.
    - exfalso.
      eapply valid_link_eq with (node := (FileNode inum)) in H0; auto.
      inversion H0.
    -  exfalso.
      eapply valid_link_eq with (node := (DirNode inum)) in H0; auto.
      inversion H0.
    - 
      eapply valid_link_eq in H0; eauto.
      inversion H0; subst. clear H0.
      erewrite <- IHpath_evaluates1 with (node' := symtarget0) in H9.
      apply IHpath_evaluates2; auto.
      auto.
      auto.
Qed.
  

Lemma path_eval_root_eq: forall pn fs node node',
    fs_invariant fs ->
    path_eval_root fs pn node ->
    path_eval_root fs pn node' ->
    node = node'.
Proof.
  intros.
  eapply path_evaluates_eq; eauto.
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
  + eapply PathEvalFileLink; eauto.
    edestruct H.
    (* validlink constructors: *)
    - constructor; simpl.
      apply Graph.add_spec; auto.
    - apply ValidDot.
    - eapply ValidDotDot.
      apply Graph.add_spec; auto.
      right; eauto.
    - apply ValidDotDotRoot; auto.
  + eapply PathEvalDirLink; eauto.
    edestruct H.
    - constructor; simpl.
      apply Graph.add_spec; auto.
    - apply ValidDot.
    - eapply ValidDotDot.
      apply Graph.add_spec; auto.
      right; eauto.
    - apply ValidDotDotRoot; auto.
  + inversion H; subst.
    eapply PathEvalSymlink; simpl.
    - constructor.
      apply Graph.add_spec.
      eauto.
    - apply IHpath_evaluates1; eauto.
    - apply IHpath_evaluates2; eauto.
Qed.

Lemma path_eval_root_addlink' : forall fs dirnum0 dirnum name dirpn n node',
  fs_invariant fs ->
  path_eval_root fs dirpn (DirNode dirnum0) ->
  path_eval_root (add_link dirnum n name fs) dirpn node' ->
  path_eval_root fs dirpn node'.
Proof.
  unfold path_eval_root, add_link in *.
  simpl in *.
  intros.
Admitted.

Lemma path_eval_root_updfile : forall fs dirnum h data dirpn,
  path_eval_root fs dirpn (DirNode dirnum) ->
  path_eval_root (upd_file h data fs) dirpn (DirNode dirnum).
Proof.
  intros.
  unfold path_eval_root, upd_file; simpl.
  induction H.
  + constructor.
  + eapply PathEvalFileLink; eauto.
    edestruct H.
    - constructor; simpl; auto.
    - apply ValidDot.
    - eapply ValidDotDot; simpl; eauto.
    - apply ValidDotDotRoot; auto.
  + eapply PathEvalDirLink; eauto.
    edestruct H.
    - constructor; simpl; auto.
    - apply ValidDot.
    - eapply ValidDotDot; simpl; eauto.
    - apply ValidDotDotRoot; auto.
  + eapply PathEvalSymlink; simpl.
    inversion H. constructor. eauto.
    apply IHpath_evaluates1; eauto.
    apply IHpath_evaluates2; eauto.
Qed.

Lemma path_evaluates_updfile' : forall fs node h data dirpn startdir,
  path_evaluates (upd_file h data fs) startdir dirpn node ->
  path_evaluates fs startdir dirpn node.
Proof.
  intros.
  match goal with
  | H : path_evaluates ?fs0 ?dir0 ?pn0 ?node0 |- _ =>
    remember fs0;
    induction H; intros; subst; simpl
  end.
  + constructor.
  + eapply PathEvalFileLink; eauto.
    inversion H; clear H; subst.
    constructor. eauto.
  + eapply PathEvalDirLink; eauto.
    inversion H; clear H; subst.
    - constructor. eauto.
    - apply ValidDot.
    - eapply ValidDotDot; simpl; eauto.
    - apply ValidDotDotRoot; auto.
  + eapply PathEvalSymlink; simpl.
    inversion H; clear H; subst.
    constructor; eauto.
    eapply IHpath_evaluates1; eauto.
    apply IHpath_evaluates2; eauto.
Qed.

Lemma path_eval_root_updfile' : forall fs node h data dirpn,
  path_eval_root (upd_file h data fs) dirpn node ->
  path_eval_root fs dirpn node.
Proof.
  intros.
  eapply path_evaluates_updfile'; eauto.
Qed.

Lemma fs_invariant_create : forall dirnum h name fs,
    name <> "." ->
    name <> ".." ->
    does_not_exist fs dirnum name ->
    file_handle_unused fs h ->
    file_handle_valid fs h ->
    fs_invariant fs ->
    fs_invariant (create_file dirnum h name fs).
Proof.
  unfold fs_invariant.
  intros.

  unfold unique_dirents; intros.

  repeat match goal with
  | H : valid_link _ _ _ _ |- _ =>
    inversion H; clear H; subst
  | H : Graph.In _ _ |- _ =>
    apply Graph.add_spec in H; intuition idtac
  | H : mkLink _ _ _ = mkLink _ _ _ |- _ =>
    inversion H; clear H; subst
  | _ =>
    solve [ exfalso; eauto ]
  | _ =>
    eauto
  end.
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

Lemma valid_link_updfile' : forall fs h data dir name target,
  valid_link (upd_file h data fs) dir name target ->
  valid_link fs dir name target.
Proof.
  intros.
  remember (upd_file h data fs); generalize dependent fs.
  induction H; intros; subst.
  - constructor. eauto.
  - eapply ValidDot.
  - eapply ValidDotDot. eauto.
  - eapply ValidDotDotRoot. eauto.
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

  eapply path_eval_root_addlink' in H8 as H8x.
  eapply path_eval_root_updfile' in H8x.
  eapply path_eval_root_eq; eauto.

  unfold fs_invariant, unique_dirents; intros.
  apply valid_link_updfile' in H9.
  apply valid_link_updfile' in H10.
  eapply H6; eauto.

  eapply path_eval_root_updfile; eauto.
Qed.



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

        
        admit.

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
