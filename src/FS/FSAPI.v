Require Import POCS.
Require Import String.
Require Import Equalities.
Require Import MSets.MSetWeakList.
Require Import Relations.Relation_Operators.
Require Import RelationClasses.
Require Import Morphisms.


Import ListNotations.
Open Scope string.

(** Data types *)

Inductive Node :=
| DirNode : forall (dirnum : nat), Node
| FileNode : forall (filenum : nat), Node
| SymlinkNode : forall (target : list string), Node.

Record Link := mkLink {
  LinkFrom : nat;   (* Always a DirNode *)
  LinkTo : Node;
  LinkName : string
}.

Instance Node_equal_dec : EqualDec Node.
  unfold EqualDec; intros.
  destruct x, y; try (right; congruence).
  destruct (eq_nat_dec dirnum dirnum0); subst; eauto.
    right; congruence.
  destruct (eq_nat_dec filenum filenum0); subst; eauto.
    right; congruence.
  destruct (list_eq_dec string_dec target target0); subst; eauto.
    right; congruence.
Defined.

Lemma Link_equal_dec : EqualDec Link.
  unfold EqualDec; intros.
  destruct x, y.
  destruct (eq_nat_dec LinkFrom0 LinkFrom1); subst.
  destruct (Node_equal_dec LinkTo0 LinkTo1); subst.
  destruct (string_dec LinkName0 LinkName1); subst.
  eauto.
  right; congruence.
  right; congruence.
  right; congruence.
Defined.

Module MDT_Link.
  Definition t := Link.
  Definition eq_dec := Link_equal_dec.
End MDT_Link.

Module Link_as_UDT := Make_UDT(MDT_Link).

Module Graph := MSetWeakList.Make Link_as_UDT.

Definition File := string.
Definition Files := list File.

Record FS := mkFS {
  FSRoot : nat;     (* root DirNode *)
  FSLinks : Graph.t;
  FSFiles : Files;  (* [filenum]s point into this list *)
}.

Definition Pathname := list string.

Definition FSEquiv (fs1 fs2 : FS) : Prop :=
  FSRoot fs1 = FSRoot fs2 /\
  FSFiles fs1 = FSFiles fs2 /\
  Graph.Equal (FSLinks fs1) (FSLinks fs2).

Instance FSEquiv_Equiv : Equivalence FSEquiv.
Proof.
  split; unfold FSEquiv.
  - intros f; intuition eauto.
    reflexivity.
  - intros f1 f2; intuition eauto.
    symmetry. eauto.
  - intros f1 f2 f3; intuition eauto.
    congruence.
    congruence.
    etransitivity; eauto.
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

(** [path_evaluates] is used to specify lookup *)

Inductive valid_link : forall (fs : FS) (dir : nat) (name : string) (target : Node), Prop :=
| ValidLink : forall fs dir name target,
  Graph.In (mkLink dir target name) (FSLinks fs) ->
  valid_link fs dir name target
| ValidDot : forall fs dir,
  valid_link fs dir "." (DirNode dir)
| ValidDotDot : forall fs dir name parent,
  Graph.In (mkLink parent (DirNode dir) name) (FSLinks fs) ->
  valid_link fs dir ".." (DirNode parent)
| ValidDotDotRoot : forall fs dir,
  dir = FSRoot fs ->
  valid_link fs dir ".." (DirNode dir).

Instance valid_link_proper :
  Proper (FSEquiv ==> eq ==> eq ==> eq ==> iff) valid_link.
Proof.
  intros fs1 fs2 H.
  intros ? ? ?; subst.
  intros ? ? ?; subst.
  intros ? ? ?; subst.
  unfold FSEquiv in H; intuition idtac.
  - inversion H1.
    + eapply ValidLink.
      eapply H2; eauto.
    + eapply ValidDot.
    + eapply ValidDotDot.
      eapply H2; eauto.
    + eapply ValidDotDotRoot. congruence.
  - inversion H1.
    + eapply ValidLink.
      eapply H2; eauto.
    + eapply ValidDot.
    + eapply ValidDotDot.
      eapply H2; eauto.
    + eapply ValidDotDotRoot. congruence.
Qed.

Inductive path_evaluates : forall (fs : FS) (start : Node) (pn : Pathname) (target : Node), Prop :=
| PathEvalEmpty : forall fs start,
  path_evaluates fs start nil start
| PathEvalFileLink : forall fs startdir name inum,
  valid_link fs startdir name (FileNode inum)  ->
  path_evaluates fs (DirNode startdir) ([name]) (FileNode inum)
| PathEvalDirLink : forall fs startdir name inum pn namenode,
  valid_link fs startdir name (DirNode inum) ->
  path_evaluates fs (DirNode inum) pn namenode ->
  path_evaluates fs (DirNode startdir) (name :: pn) namenode
| PathEvalSymlink : forall fs startdir name sympath symtarget pn target,
  valid_link fs startdir name (SymlinkNode sympath) ->
  path_evaluates fs (DirNode startdir) sympath symtarget ->
  path_evaluates fs symtarget pn target ->
  path_evaluates fs (DirNode startdir) (name :: pn) target.

Instance path_evaluates_proper :
  Proper (FSEquiv ==> eq ==> eq ==> eq ==> iff) path_evaluates.
Proof.
  intros fs1 fs2 H.
  intros ? ? ?; subst.
  intros ? ? ?; subst.
  intros ? ? ?; subst.
  intuition.
  - induction H0.
    + eapply PathEvalEmpty.
    + eapply PathEvalFileLink; eauto.
      rewrite H in H0. eauto.
    + eapply PathEvalDirLink; eauto.
      rewrite H in H0. eauto.
    + eapply PathEvalSymlink; eauto.
      rewrite H in H0; eauto.
  - induction H0.
    + eapply PathEvalEmpty.
    + eapply PathEvalFileLink; eauto.
      rewrite <- H in H0. eauto.
    + eapply PathEvalDirLink; eauto.
      rewrite <- H in H0. eauto.
    + eapply PathEvalSymlink; eauto.
      rewrite <- H in H0; eauto.
Qed.

Definition path_eval_root (fs : FS) (pn : Pathname) (target : Node) : Prop :=
  path_evaluates fs (DirNode (FSRoot fs)) pn target.

Instance path_eval_root_proper :
  Proper (FSEquiv ==> eq ==> eq ==> iff) path_eval_root.
Proof.
  intros fs1 fs2 H.
  intros ? ? ?; subst.
  intros ? ? ?; subst.
  unfold path_eval_root.
  eapply path_evaluates_proper; eauto.
  unfold FSEquiv in *; intuition.
Qed.

Hint Constructors valid_link.
Hint Constructors path_evaluates.

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

(* If pn exists, then it is unique. *)
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

(** This invariant isn't always true: a rename of a file in the same directory,
 will add the destination before deleting it, since we model rename as
 link+unlink. thus, a lookup may observe a duplicate entry after the link and
 before the unlink. so, path_evaluates_unique isn't true either. *)
Definition fs_invariant (fs : FS) :=
  unique_dirents fs.

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

Lemma valid_link_addlink_does_not_exists: forall fs dirnum name h node' node'' startdir name0,
    name <> "." ->
    name <> ".." ->
    fs_invariant fs ->
    does_not_exist fs dirnum name ->
    valid_link fs startdir name0 node'' ->
    valid_link (add_link dirnum (FileNode h) name fs) startdir name0 node' ->
    valid_link fs startdir name0 node'.
Proof.
  intros.
  inversion H4; subst.
  apply Graph.add_spec in H5.
  intuition; subst. 
  inversion H6; subst. clear H6.
  destruct H2.
  eexists.
  inversion H3; subst; eauto; try congruence.
  apply ValidDot.
  eapply ValidDotDot.
  apply Graph.add_spec in H5.
  intuition; subst; try congruence.
  eauto.
  eapply ValidDotDotRoot.
  unfold add_link; simpl; auto.
Qed.

Lemma path_evaluates_addlink_does_not_exists: forall fs dirnum name h node' node'' startdir path,
    name <> "." ->
    name <> ".." ->
    fs_invariant fs ->
    does_not_exist fs dirnum name ->
    path_evaluates fs (DirNode startdir) path node'' ->
    path_evaluates (add_link dirnum (FileNode h) name fs) (DirNode startdir) path node' ->
    path_evaluates fs (DirNode startdir) path node'.
Proof.
  intros.
  remember ((add_link dirnum (FileNode h) name fs)).
  generalize dependent fs.
  generalize dependent node''.
  induction H4; intros; subst.
  + constructor.
  + apply PathEvalFileLink.
    eapply valid_link_addlink_does_not_exists in H1; eauto.
    inversion H4; subst; eauto.
    inversion H11; subst; eauto.
    eapply valid_link_addlink_does_not_exists in H1; eauto.
    eapply H2 in H1.
    apply H1 in  H9.
    congruence.
  + inversion H5; subst; eauto.

    eapply valid_link_addlink_does_not_exists in H1; eauto.

    eapply PathEvalDirLink; eauto.
    eapply valid_link_addlink_does_not_exists in H1; eauto.
    eapply valid_link_eq with (node := (DirNode inum0)) in H1; eauto.
    inversion H1; subst.
    eapply IHpath_evaluates; eauto.

    eapply valid_link_addlink_does_not_exists in H1; eauto.
    eapply H2 in H1.
    apply H1 in  H10.
    congruence.

  + inversion H4; subst; auto.
    
    eapply valid_link_addlink_does_not_exists in H1; eauto.
    eapply H2 in H1.
    apply H1 in  H10.
    congruence.

    eapply valid_link_addlink_does_not_exists in H1; eauto.
    eapply H2 in H1.
    apply H1 in  H9.
    congruence.

    eapply PathEvalSymlink; eauto.

    eapply valid_link_addlink_does_not_exists in H1; eauto.
    eapply valid_link_eq with (node := (SymlinkNode sympath0)) in H1; eauto.
    inversion H1; subst. clear H1.

    replace symtarget0 with symtarget in *; eauto.
    eapply path_evaluates_eq; try eassumption.
    eapply IHpath_evaluates1; eauto.
Qed.

Lemma path_eval_addlink' : forall fs startdir dirpn dirnum h name node',
    name <> "." ->
    name <> ".." ->
    fs_invariant fs ->
    does_not_exist fs dirnum name ->
    path_evaluates fs startdir dirpn (DirNode dirnum) ->
    path_evaluates (add_link dirnum (FileNode h) name fs) startdir dirpn node' ->
    node' = (DirNode dirnum).
Proof.
  intros.
  generalize dependent fs; intros.
  induction H3.
  + inversion H4; subst.
    constructor.
  + inversion H4; subst. clear H4.
    eapply valid_link_addlink_does_not_exists in H8; eauto.
    eapply valid_link_addlink_does_not_exists in H9; eauto.
    exfalso.
    eapply H1 in H3.
    eapply H3 in H9.
    congruence.

    eapply valid_link_addlink_does_not_exists in H9; eauto.
    exfalso.
    eapply H1 in H3.
    eapply H3 in H9.
    congruence.
    
  + inversion H4; subst. clear H4.
    eapply valid_link_addlink_does_not_exists in H11; eauto.
    exfalso.
    eapply H1 in H3.
    eapply H3 in H11.
    congruence.

    eapply valid_link_addlink_does_not_exists in H10; eauto.
    eapply H1 in H3.
    eapply H3 in H10.
    inversion H10; subst. clear H10.
    apply IHpath_evaluates; eauto.

    
    eapply valid_link_addlink_does_not_exists in H10; eauto.
    eapply H1 in H3.
    eapply H3 in H10.
    inversion H10.
    
  + inversion H4; subst. clear H4.
    eapply valid_link_addlink_does_not_exists in H10; eauto.
    exfalso.
    eapply H1 in H3.
    eapply H3 in H10.
    congruence.

    eapply valid_link_addlink_does_not_exists in H9; eauto.
    exfalso.
    eapply H1 in H3.
    eapply H3 in H9.
    congruence.

    eapply valid_link_addlink_does_not_exists in H9; eauto.
    eapply H1 in H3.
    eapply H3 in H9. clear H3.
    inversion H9; subst. clear H9.
    intuition idtac.
    apply H3.
    replace symtarget with symtarget0; eauto.
    eapply path_evaluates_eq. eassumption.
    2: eassumption.
    eapply path_evaluates_addlink_does_not_exists; eauto.
Qed.

Lemma path_eval_root_addlink' : forall fs dirnum name dirpn h node,
    name <> "." ->
    name <> ".." ->
    fs_invariant fs ->
    does_not_exist fs dirnum name ->
    path_eval_root fs dirpn (DirNode dirnum) ->
    path_eval_root (add_link dirnum (FileNode h) name fs) dirpn node ->
    path_eval_root fs dirpn node.
Proof.
  unfold path_eval_root.
  intros.
  eapply path_eval_addlink' in H4; subst; eauto.
Qed.
  
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

(* File system operations *)

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


(* Semantics of file system operations *)

Definition State := FS.

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

Inductive fs_step : forall T, fsOpT T -> nat -> State -> T -> State -> Prop :=
| StepCreate : forall dir dirnum name tid s h s',
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

Hint Constructors fs_step.

Definition fs_step_equiv : OpSemantics fsOpT State :=
  equiv_step fs_step FSEquiv.

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

