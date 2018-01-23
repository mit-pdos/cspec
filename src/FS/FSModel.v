Require Import POCS.
Require Import String.
Require Import Equalities.
Require Import MSets.MSetWeakList.
Require Import Relations.Relation_Operators.
Require Import RelationClasses.
Require Import Morphisms.
Require Import Sumbool.

Import ListNotations.
Open Scope string.

(** Declarative spec for a FS interface with concurrent operations, modeled
 after POCS notes.  The file system is represented as set of links.  To allow
 for concurrent operations a directory may contain a link with the same name
 twice, but for different nodes.  For example, we model a rename as a link
 followed by an unlink.  Thus, a lookup after link and before unlink may observe
 a duplicate name, but each name has a different node. *)


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

Definition eq_string (s1 s2 : string) :=
  if string_dec s1 s2 then true else false.

Definition proper_nameb n : bool := negb (orb (eq_string n  ".") (eq_string n "..")).
Definition proper_name n := n <> "." /\ n <> "..".
Definition proper_link l := proper_name (LinkName l).
Definition proper_links g := Graph.For_all proper_link g.
Instance proper_proper_link:
  Proper (eq ==> eq) proper_link.
Proof.
  intros ? ?.
  intros; subst; reflexivity.
Qed.

Lemma In_add_add_comm: forall a l1 l2 g,
    Graph.In a (Graph.add l1 (Graph.add l2 g)) ->
    Graph.In a (Graph.add l2 (Graph.add l1 g)).
Proof.
  intros.
  eapply Graph.add_spec in H; intuition idtac; subst.
  eapply Graph.add_spec; right. eapply Graph.add_spec; eauto.
  eapply Graph.add_spec in H0; intuition idtac; subst.
  eapply Graph.add_spec; eauto.
  eapply Graph.add_spec; right. eapply Graph.add_spec; eauto.
Qed.

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
(*
    proper_name name ->
    (exists parent name,
        Graph.In (mkLink parent (DirNode dir) name) (FSLinks fs) ->
        target <> DirNode parent) ->
*)
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

Definition proper_link' fs l := proper_name (LinkName l) /\
                             (exists parent, valid_link fs (LinkFrom l) ".." parent ->
                                (LinkTo l) <> parent).

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

Lemma path_evaluates_cons': forall fs startdir name pn node,
    path_evaluates fs startdir (name::pn) node ->
    exists node',
      path_evaluates fs startdir [name] node' /\
      path_evaluates fs node' pn node.
Proof.
  intros.
  inversion H; subst; eexists; eauto.
Qed.

Lemma path_evaluates_cons: forall fs startdir name pn node node',
    path_evaluates fs (DirNode startdir) [name] node' ->
    path_evaluates fs node' pn node ->
    exists node'',
      path_evaluates fs (DirNode startdir) (name::pn) node''.
Proof.
  intros.
  inversion H; subst; clear H.
  - eexists.
    inversion H0; subst; clear H0.
    constructor; eauto.
  - eexists.
    eapply PathEvalDirLink; eauto.
    inversion H7; subst; clear H7.
    eauto.
  - eexists.
    inversion H8; subst; clear H8.
    eapply PathEvalSymlink; eauto.
Qed.

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

Definition del_link dir node name (fs : FS) :=
  mkFS (FSRoot fs) (Graph.remove (mkLink dir node name) (FSLinks fs)) (FSFiles fs).

Definition create_file dir h name (fs : FS) :=
  add_link dir (FileNode h) name (upd_file h "" fs).

Definition valid_dir dir (fs : FS) :=
  exists pn, path_eval_root fs pn (DirNode dir).

Definition match_readdir from l :=
  beq_nat from (LinkFrom l).

Definition readdir fs dir :=
  Graph.filter (match_readdir dir) (FSLinks fs).

Definition readdir_names fs dir :=
  map LinkName (Graph.elements (readdir fs dir)).

(* If pn exists, then it is unique. *)
Definition unique_pathname (fs : FS) startdir pn :=
  exists node,
    path_evaluates fs startdir pn node /\
    forall node',
      path_evaluates fs startdir pn node' -> node' = node.

Definition unique_pathname_root (fs : FS) pn :=
  exists node,
    path_eval_root fs pn node /\
    forall node',
      path_eval_root fs pn node' -> node' = node.

Lemma unique_pathname_path_evaluates_eq: forall fs startdir pn node node',
    unique_pathname fs startdir pn ->
    path_evaluates fs startdir pn node ->
    path_evaluates fs startdir pn node' ->
    node = node'.
Proof.
  intros.
  unfold unique_pathname in *.
  deex.
  specialize (H2 node H0) as H2x; subst.
  specialize (H2 node' H1) as H2x; subst.
  reflexivity.
Qed.

Lemma unique_pathname_valid_link_eq: forall fs dirnum name inum inum',
    unique_pathname fs (DirNode dirnum) [name] ->
    valid_link fs dirnum name (DirNode inum) ->
    valid_link fs dirnum name (DirNode inum') ->
    DirNode inum = DirNode inum'.
Proof.
  intros.
  unfold unique_pathname in *.
  deex.
  specialize (H2 (DirNode inum)) as H2x; subst.
  specialize (H2 (DirNode inum')) as H2y; subst.
  destruct H2x.
  econstructor.
  eapply H0.
  constructor.
  destruct H2y.
  econstructor.
  eapply H1.
  constructor.
  reflexivity.
Qed.

Lemma unique_pathname_path_evaluates_cons_eq: forall fs startdir name pn' node node' node'',
    path_evaluates fs (DirNode startdir) [name] node' ->
    path_evaluates fs node' pn' node ->
    unique_pathname fs (DirNode startdir) [name] ->
    unique_pathname fs node' pn' ->
    path_evaluates fs (DirNode startdir) (name :: pn') node'' ->
    node = node''.
Proof.
  intros.
  eapply path_evaluates_cons' in H3 as Hcons.
  deex.
  assert (node'0 = node').
  eapply unique_pathname_path_evaluates_eq in H; eauto.
  subst.
  assert (node = node'').
  eapply unique_pathname_path_evaluates_eq in H2; eauto.
  subst.
  reflexivity.
Qed.

(* A stronger version of unique_pathname, requiring all intermediate nodes match *)
Inductive stable_pathname : forall (fs: FS) (startdir: Node) (pn: Pathname), Prop :=
| StablePathNil: forall fs startdir, stable_pathname fs (DirNode startdir) []
| StablePathCons: forall fs startdir name pn' node node',
    path_evaluates fs (DirNode startdir) [name] node' ->
    path_evaluates fs node' pn' node ->
    unique_pathname fs (DirNode startdir) [name] ->
    unique_pathname fs node' pn' ->
    stable_pathname fs (DirNode startdir) (name::pn').

(* sanity check *)
Lemma stable_pathname_unique_pathname: forall fs startdir pn,
    stable_pathname fs startdir pn ->
    unique_pathname fs startdir pn.
Proof.
  intros.
  inversion H; subst; clear H.
  - eexists.
    split.
    constructor.
    intros.
    inversion H; auto.
  - unfold unique_pathname.
    eapply path_evaluates_cons in H1 as Hcons; eauto.
    deex.
    eapply unique_pathname_path_evaluates_cons_eq in H as Hx; eauto.
    subst.
    exists node''.
    split; eauto.
    intros.
    eapply unique_pathname_path_evaluates_cons_eq in H4 as Hx; eauto.
Qed.
                               
Definition unique_dirent (fs : FS) dir name :=
  forall target target0,
    valid_link fs dir name target ->
    valid_link fs dir name target0 ->
    target0 = target.

Definition unique_dirents (fs : FS) :=
  forall dir name target target0,
    valid_link fs dir name target ->
    valid_link fs dir name target0 ->
    target0 = target.

Lemma unique_dirent_link_eq: forall fs startdir name node node',
    unique_dirent fs startdir name ->
    valid_link fs startdir name node ->
    valid_link fs startdir name node' ->
    node = node'.
Proof.
  intros.
  edestruct H; eauto.
Qed.

(* . and .. are unique; which we get from definition.
  no other name in directory refers to parent or cur directory *)

Definition fs_invariant (fs : FS) := proper_links (FSLinks fs).

(*
Definition unique_dotdot (fs : FS) :=

                  
Definition fs_invariant1 (fs : FS) := proper_links (FSLinks fs) /\
                                      unique_dotdot.
*)

Lemma fs_invariant_proper_name: forall fs startdir node name,
    fs_invariant fs ->
    Graph.In (mkLink startdir node name) (FSLinks fs) ->
    proper_name name.
Proof.
  intros.
  unfold fs_invariant in *.
  unfold proper_links in *.
  unfold Graph.For_all in *.
  specialize (H (mkLink startdir node name) H0); eauto.
Qed.

Lemma fs_invariant_add_link: forall fs dirnum name node,
    fs_invariant fs ->
    proper_name name ->
    does_not_exist fs dirnum name ->
    fs_invariant (add_link dirnum node name fs).
Proof.
  intros.
  unfold fs_invariant in *.
  unfold proper_links in *.
  unfold proper_link in *.
  unfold Graph.For_all in *.
  intros; simpl in *.
  eapply Graph.add_spec in H2; eauto.
  intuition idtac; subst; simpl in *; eauto.
Qed.

Lemma path_evaluates_add_link : forall fs startdir dirnum name dirpn n node,
  path_evaluates fs startdir dirpn node ->
  path_evaluates (add_link dirnum n name fs) startdir dirpn node.
Proof.
  unfold add_link in *.
  simpl in *.
  intros.
  induction H.
  + constructor.
  + eapply PathEvalFileLink; eauto.
    edestruct H.
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

Lemma valid_link_does_not_exist: forall fs dirnum name node,
    proper_name name ->
    valid_link fs dirnum name node ->
    does_not_exist fs dirnum name ->
    False.
Proof.
  intros.
  inversion H0; subst; clear H0.
  - destruct H1; eexists; eauto.
  - destruct H; congruence.
  - destruct H; congruence.
  - destruct H; congruence.
Qed.

Lemma path_evaluates_does_not_exist: forall fs dirnum name,
    proper_name name ->
    path_evaluates fs (DirNode dirnum) [name] (DirNode dirnum) ->
    does_not_exist fs dirnum name ->
    False.
Proof.
  intros.
  inversion H0; subst; clear H0.
  inversion H8; subst; clear H8.
  eapply valid_link_does_not_exist; eauto.
  inversion H9; subst; clear H9.
  eapply valid_link_does_not_exist; eauto.
Qed.

Lemma valid_link_add_link': forall fs startdir name name0 dirnum n node node',
    proper_name name0 ->
    valid_link fs startdir name0 node ->
    proper_name name  ->
    does_not_exist fs dirnum name ->
    valid_link (add_link dirnum n name fs) startdir name0 node' ->
    valid_link fs startdir name0 node'.
Proof.
  intros.
  inversion H3; subst; clear H3.
  - apply Graph.add_spec in H4.
    intuition idtac; auto.
    inversion H3; subst; clear H3.
    exfalso; eapply valid_link_does_not_exist; eauto.
  - apply ValidDot.
  - eapply ValidDotDot.
    apply Graph.add_spec in H4; auto.
    intuition idtac; eauto.
    inversion H3; subst. clear H3.
    inversion H; congruence.
  - eapply ValidDotDotRoot.
    simpl in *.
    reflexivity.
Qed. 

Lemma valid_link_add_link'': forall fs startdir name name0 dirnum n node node',
    valid_link fs startdir name0 node ->
    proper_name name  ->
    does_not_exist fs dirnum name ->
    valid_link (add_link dirnum n name fs) startdir name0 node' ->
    valid_link fs startdir name0 node'.
Proof.
  intros.
  inversion H2; subst; clear H2.
  - apply Graph.add_spec in H3.
    intuition idtac; auto.
    inversion H2; subst; clear H2.
    exfalso; eapply valid_link_does_not_exist; eauto.
  - apply ValidDot.
  - eapply ValidDotDot.
    apply Graph.add_spec in H3; auto.
    intuition idtac; eauto.
    inversion H2; subst. clear H2.
    admit. 
  - eapply ValidDotDotRoot.
    simpl in *.
    reflexivity.
Admitted. 

Lemma path_evaluates_add_link' : forall fs startdir dirnum name dirpn n node,
  fs_invariant fs ->
  stable_pathname fs startdir dirpn ->
  path_evaluates fs startdir dirpn (DirNode dirnum) ->
  does_not_exist fs dirnum name  ->
  proper_name name ->
  path_evaluates (add_link dirnum n name fs) startdir dirpn node ->
  path_evaluates fs startdir dirpn node.
Proof.
  intros.
  remember (add_link dirnum n name fs).
  generalize dependent fs; intros.
  induction H4; subst.
  - constructor.
  - eapply PathEvalFileLink; subst; eauto.
    inversion H4; subst.
    eapply fs_invariant_proper_name in H5 as H5x.
    eapply Graph.add_spec in H5.
    intuition idtac.
    + inversion H6; subst; clear H6.
      eapply path_evaluates_does_not_exist in H2; eauto.
      exfalso; auto.
    + constructor; eauto.
    + apply fs_invariant_add_link; eauto.
  - inversion H1; subst; clear H1.
    {
      eapply PathEvalDirLink; eauto.
      eapply valid_link_add_link'' in H4; auto.
      assert (DirNode inum0 = DirNode inum).
      {
        inversion H0; subst.
        eapply unique_pathname_valid_link_eq.
        eapply H13.
        eauto.
        eauto.
      }
      inversion H1; subst; clear H1.
      eapply IHpath_evaluates; eauto.
      admit.
      eauto.
    }
    {
      inversion H10; subst.
      eapply fs_invariant_proper_name in H1 as Hx; eauto.
      eapply valid_link_add_link'' in H4; eauto.
      exfalso. admit. (* H2 + H8 + H *)
    }
  - eapply PathEvalSymlink; eauto; subst.
    inversion H0; subst.
    (*
    - constructor.
      apply Graph.add_spec.
      eauto.
    - apply IHpath_evaluates1; eauto.
    - apply IHpath_evaluates2; eauto.
*)
Admitted.

Lemma path_eval_root_add_link : forall fs dirnum name dirpn n,
  path_eval_root fs dirpn (DirNode dirnum) ->
  path_eval_root (add_link dirnum n name fs) dirpn (DirNode dirnum).
Proof.
  intros.
  unfold path_eval_root.
  eapply path_evaluates_add_link in H; eauto.
Qed.

Lemma path_evaluates_upd_file : forall fs startdir dirnum h data dirpn,
  path_evaluates fs startdir dirpn (DirNode dirnum) ->
  path_evaluates (upd_file h data fs) startdir dirpn (DirNode dirnum).
Proof.
  intros.
  unfold upd_file; simpl.
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

Lemma path_eval_root_upd_file : forall fs dirnum h data dirpn,
  path_eval_root fs dirpn (DirNode dirnum) ->
  path_eval_root (upd_file h data fs) dirpn (DirNode dirnum).
Proof.
  intros.
  unfold path_eval_root in *.
  eapply path_evaluates_upd_file in H; eauto.
Qed.

Lemma path_evaluates_upd_file' : forall fs node h data dirpn startdir,
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

Lemma path_eval_root_upd_file' : forall fs node h data dirpn,
  path_eval_root (upd_file h data fs) dirpn node ->
  path_eval_root fs dirpn node.
Proof.
  intros.
  eapply path_evaluates_upd_file'; eauto.
Qed.

Lemma does_not_exist_add_link : forall fs dirnum name dirnum0 n0 name0,
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
  
Lemma does_not_exist_add_link_same_dirnum : forall fs dirnum name n0 name0,
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
  
Lemma does_not_exist_upd_file : forall fs h data dirnum name,
  does_not_exist (upd_file h data fs) dirnum name ->
  does_not_exist fs dirnum name.
Proof.
  intros.
  unfold does_not_exist, upd_file in *.
  simpl in *; auto.
Qed.

Lemma does_not_exist_upd_file' : forall fs h data dirnum name,
  does_not_exist fs dirnum name ->
  does_not_exist (upd_file h data fs) dirnum name.
Proof.
  intros.
  unfold does_not_exist, upd_file in *.
  simpl in *; auto.
Qed.
  
Hint Resolve does_not_exist_add_link.
Hint Resolve does_not_exist_add_link_same_dirnum.
Hint Resolve does_not_exist_upd_file.
Hint Resolve does_not_exist_upd_file'.

Lemma file_handle_unused_upd_file : forall fs h0 data0 h,
  file_handle_unused (upd_file h0 data0 fs) h ->
  file_handle_unused fs h.
Proof.
  intros.
  unfold file_handle_unused, upd_file in *.
  simpl in *; auto.
Qed.

Lemma file_handle_unused_add_link : forall fs dirnum n name h,
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
  
Lemma file_handle_unused_upd_file' : forall fs h0 data0 h,
  file_handle_unused fs h ->
  file_handle_unused (upd_file h0 data0 fs) h.
Proof.
  intros.
  unfold file_handle_unused, upd_file in *.
  simpl in *; auto.
Qed.

Lemma file_handle_unused_add_link' : forall fs dirnum n name h,
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

Hint Resolve file_handle_unused_upd_file.
Hint Resolve file_handle_unused_add_link.
Hint Resolve file_handle_unused_add_link'.
Hint Resolve file_handle_unused_ne.

Lemma file_handle_valid_upd_file : forall fs h0 data0 h,
  file_handle_valid (upd_file h0 data0 fs) h ->
  file_handle_valid fs h.
Proof.
  intros.
  unfold file_handle_valid, file_handle_valid, upd_file in *.
  simpl in *.
  rewrite length_list_upd in H; auto.
Qed.

Lemma file_handle_valid_add_link : forall fs dirnum n name h,
  file_handle_valid (add_link dirnum n name fs) h ->
  file_handle_valid fs h.
Proof.
  intros.
  unfold file_handle_valid, file_handle_valid, add_link in *.
  simpl in *; auto.
Qed.

Lemma file_handle_valid_upd_file' : forall fs h0 data0 h,
  file_handle_valid fs h ->
  file_handle_valid (upd_file h0 data0 fs) h.
Proof.
  intros.
  unfold file_handle_valid, file_handle_valid, upd_file in *.
  simpl in *.
  rewrite length_list_upd; auto.
Qed.
  
Lemma file_handle_valid_add_link' : forall fs dirnum n name h,
  file_handle_valid fs h ->
  file_handle_valid (add_link dirnum n name fs) h.
Proof.
  intros.
  unfold file_handle_valid, file_handle_valid, add_link in *.
  simpl in *; auto.
Qed.
  
Hint Resolve file_handle_valid_upd_file.
Hint Resolve file_handle_valid_add_link.
Hint Resolve file_handle_valid_upd_file'.
Hint Resolve file_handle_valid_add_link'.

Lemma valid_link_upd_file' : forall fs h data dir name target,
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

