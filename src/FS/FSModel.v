Require Import POCS.
Require Import String.
Require Import Equalities.
Require Import Relations.Relation_Operators.
Require Import RelationClasses.
Require Import Morphisms.
Require Import Sumbool.
Require Import ProofIrrelevance.

Import ListNotations.
Open Scope string.

(** Declarative spec for a FS interface with concurrent operations, modeled
 after POCS notes.  The file system is represented as set of links.  To allow
 for concurrent operations a directory may contain a link with the same name
 twice, but for different nodes.  For example, we model a rename as a link
 followed by an unlink.  Thus, a lookup after link and before unlink may observe
 a duplicate name, but each name has a different node. Similarly, there may be
 several ".." entries pointing to different parents. *)

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
Proof.
  unfold EqualDec.
  decide equality;
    match goal with
    | [ |- {?x = ?y} + {_} ] =>
      destruct (x == y); eauto
    end.
Defined.

Lemma Link_equal_dec : EqualDec Link.
  unfold EqualDec.
  decide equality;
    match goal with
    | [ |- {?x = ?y} + {_} ] =>
      destruct (x == y); eauto
    end.
Defined.

Instance Node_Ordering : Ordering Node.
Proof.
  eapply (injection_Ordering (nat + nat + list string)).
  typeclasses eauto.
  unshelve econstructor; intros.
  destruct H; [ left; left | left; right | right ]; eauto.
  destruct x, y; simpl in *; congruence.
Defined.

Instance Link_Ordering : Ordering Link.
Proof.
  eapply (injection_Ordering (nat * Node * string)%type).
  typeclasses eauto.

  unshelve econstructor; intros.
  exact (H.(LinkFrom), H.(LinkTo), H.(LinkName)).
  destruct x, y; simpl in *; congruence.
Defined.

Definition eq_string (s1 s2 : string) :=
  if string_dec s1 s2 then true else false.

Definition proper_name n := n <> "." /\ n <> "..".
Definition proper_link l := proper_name (LinkName l).
Definition proper_links g := FSet.For_all proper_link g.

Inductive PFSet: forall ls, Prop :=
| LSProperNames: forall ls,
    proper_links ls ->
    PFSet ls.

Definition File := string.
Definition Files := list File.

Record FS := mkFS {
  FSRoot : nat;     (* root DirNode *)
  FSLinks : FSet.t Link;
  FSFiles : Files;  (* [filenum]s point into this list *)
}.

Definition Pathname := list string.

(** [path_evaluates] is used to specify lookup *)

Inductive valid_link : forall (fs : FS) (dir : nat) (name : string) (target : Node), Prop :=
| ValidLink : forall fs dir name target,
    FSet.In (mkLink dir target name) (FSLinks fs) ->
    valid_link fs dir name target
| ValidDot : forall fs dir,
    valid_link fs dir "." (DirNode dir)
| ValidDotDot : forall fs dir name parent,
    FSet.In (mkLink parent (DirNode dir) name) (FSLinks fs) ->
    valid_link fs dir ".." (DirNode parent)
| ValidDotDotRoot : forall fs dir,
    dir = FSRoot fs ->
    valid_link fs dir ".." (DirNode dir).

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

Definition path_eval_root (fs : FS) (pn : Pathname) (target : Node) : Prop :=
  path_evaluates fs (DirNode (FSRoot fs)) pn target.

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
  ~ exists n, FSet.In (mkLink dirnum n name) (FSLinks fs).

Definition file_handle_unused (fs : FS) h :=
  ~ exists d name, FSet.In (mkLink d (FileNode h) name) (FSLinks fs).

Definition file_handle_valid (fs : FS) h :=
  h < Datatypes.length (FSFiles fs).

Definition upd_file h data (fs : FS) :=
  mkFS (FSRoot fs) (FSLinks fs) (list_upd (FSFiles fs) h data).

Definition add_link dir node name (fs : FS) :=
  mkFS (FSRoot fs) (FSet.add (mkLink dir node name) (FSLinks fs)) (FSFiles fs).

Definition del_link dir node name (fs : FS) :=
  mkFS (FSRoot fs) (FSet.remove (mkLink dir node name) (FSLinks fs)) (FSFiles fs).

Definition create_file dir h name (fs : FS) :=
  add_link dir (FileNode h) name (upd_file h "" fs).

Definition valid_dir dir (fs : FS) :=
  exists pn, path_eval_root fs pn (DirNode dir).

Definition match_readdir from l :=
  beq_nat from (LinkFrom l).

Definition readdir fs dir :=
  FSet.filter (match_readdir dir) (FSLinks fs).

Definition readdir_names fs dir :=
  map LinkName (FSet.elements (readdir fs dir)).

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

Definition fs_invariant (fs : FS) := proper_links (FSLinks fs).

Lemma fs_proper_name: forall fs startdir node name,
    fs_invariant fs ->
    FSet.In (mkLink startdir node name) (FSLinks fs) ->
    proper_name name.
Proof.
  intros.
  unfold fs_invariant in *.
  unfold proper_links in *.
  eapply FSet.For_all_in in H; eauto.
  auto.
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
  eapply FSet.add_forall; eauto.
Qed.

Hint Resolve FSet.add_incr.
Hint Constructors valid_link.

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
    edestruct H; eauto.
    - constructor; simpl; auto.
    - eapply ValidDotDot.
      eapply FSet.add_incr; eauto.
  + eapply PathEvalDirLink; eauto.
    edestruct H; eauto.
    - constructor; simpl; eauto.
    - eapply ValidDotDot.
      apply FSet.add_incr; eauto.
  + inversion H; subst.
    eapply PathEvalSymlink; simpl; eauto.
    constructor.
    apply FSet.add_incr; eauto.
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

Lemma valid_link_add_file_link': forall fs startdir name name0 dirnum node node' inum,
    valid_link fs startdir name0 node ->
    proper_name name  ->
    does_not_exist fs dirnum name ->
    valid_link (add_link dirnum (FileNode inum) name fs) startdir name0 node' ->
    valid_link fs startdir name0 node'.
Proof.
  intros.
  inversion H2; subst; clear H2; eauto.
  - apply FSet.add_in' in H3; intuition eauto.
    inversion H2; subst; clear H2.
    exfalso; eapply valid_link_does_not_exist; eauto.
  - eapply ValidDotDot.
    apply FSet.add_in' in H3; auto.
    intuition idtac; eauto.
    inversion H2.
Qed.

Lemma path_evaluates_add_link' : forall fs startdir dirnum name dirpn finum node,
  fs_invariant fs ->
  stable_pathname fs startdir dirpn ->
  path_evaluates fs startdir dirpn (DirNode dirnum) ->
  does_not_exist fs dirnum name  ->
  proper_name name ->
  path_evaluates (add_link dirnum (FileNode finum) name fs) startdir dirpn node ->
  path_evaluates fs startdir dirpn node.
Proof.
  intros.
  remember (add_link dirnum (FileNode finum) name fs).
  generalize dependent fs; intros.
  induction H4; subst.
  - constructor.
  - eapply PathEvalFileLink; subst; eauto.
    inversion H4; subst.
    eapply fs_proper_name in H5 as H5x.
    eapply FSet.add_in' in H5.
    intuition idtac.
    + inversion H6; subst; clear H6.
      exfalso; eauto using path_evaluates_does_not_exist.
    + constructor; eauto.
    + apply fs_invariant_add_link; eauto.
  - inversion H1; subst; clear H1.
    {
      eapply PathEvalDirLink; eauto.
      eapply valid_link_add_file_link' in H4; auto.
      assert (DirNode inum0 = DirNode inum).
      {
        inversion H0; subst.
        eauto using unique_pathname_valid_link_eq.
      }
      inversion H1; subst; clear H1.
      eapply IHpath_evaluates; eauto.
      admit.
      eauto.
    }
    {
      inversion H10; subst.
      eapply fs_proper_name in H1 as Hx; eauto.
      (* stronger property on dirpn  *)
      (* xxx eapply valid_link_add_link'' in H4; eauto. *)
      exfalso. admit. (* H2 + H8 + H *)
    }
  - eapply PathEvalSymlink; eauto; subst.
    inversion H0; subst.
    (*
    - constructor.
      apply FSet.add_spec.
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

Hint Constructors path_evaluates.

Lemma path_evaluates_upd_file : forall fs startdir dirnum h data dirpn,
  path_evaluates fs startdir dirpn (DirNode dirnum) ->
  path_evaluates (upd_file h data fs) startdir dirpn (DirNode dirnum).
Proof.
  intros.
  unfold upd_file; simpl.
  induction H; eauto.
  + eapply PathEvalFileLink.
    edestruct H; eauto.
  + eapply PathEvalDirLink; eauto.
    destruct H; eauto.
  + eapply PathEvalSymlink; simpl; eauto.
    destruct H; eauto.
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
  apply FSet.add_incr; eauto.
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
  apply FSet.add_in' in H1.
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
  apply FSet.add_incr; eauto.
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
  apply FSet.add_in' in H1.
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
  rewrite H0 in *.
  apply FSet.add_in.
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

