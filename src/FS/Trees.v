Require Import POCS.
Require Import String.

Import ListNotations.
Open Scope string.


Inductive Node :=
| DirNode : forall (dirnum : nat), Node
| FileNode : forall (filenum : nat), Node
| SymlinkNode : forall (target : list string), Node.

Record Link := mkLink {
  LinkFrom : nat;   (* Always a DirNode *)
  LinkTo : Node;
  LinkName : string
}.

Definition Graph := list Link.

Definition File := list nat.
Definition Files := list File.

Record FS := mkFS {
  FSRoot : nat;     (* root DirNode *)
  FSLinks : Graph;
  FSFiles : Files;  (* [filenum]s point into this list *)
}.

Definition Pathname := list string.

Inductive valid_link : forall (fs : FS) (dir : nat) (name : string) (target : Node), Prop :=
| ValidLink : forall fs dir name target,
  In (mkLink dir target name) (FSLinks fs) ->
  valid_link fs dir name target
| ValidDot : forall fs dir,
  valid_link fs dir "." (DirNode dir)
| ValidDotDot : forall fs dir name parent,
  In (mkLink parent (DirNode dir) name) (FSLinks fs) ->
  valid_link fs dir ".." (DirNode parent)
| ValidDotDotRoot : forall fs dir,
  dir = FSRoot fs ->
  valid_link fs dir ".." (DirNode dir).

Inductive path_evaluates : forall (fs : FS) (start : Node) (pn : Pathname) (target : Node), Prop :=
| PathEvalEmpty : forall fs start,
  path_evaluates fs start nil start
| PathEvalLink : forall fs startdir name namenode pn target,
  valid_link fs startdir name namenode ->
  path_evaluates fs namenode pn target ->
  path_evaluates fs (DirNode startdir) (name :: pn) target
| PathEvalSymlink : forall fs startdir name sympath symtarget pn target,
  In (mkLink startdir (SymlinkNode sympath) name) (FSLinks fs) ->
  path_evaluates fs (DirNode startdir) sympath symtarget ->
  path_evaluates fs symtarget pn target ->
  path_evaluates fs (DirNode startdir) (name :: pn) target.

Definition path_eval_root (fs : FS) (pn : Pathname) (target : Node) : Prop :=
  path_evaluates fs (DirNode (FSRoot fs)) pn target.


(** Largely boilerplate helpers *)

Hint Constructors valid_link.
Hint Constructors path_evaluates.
Hint Resolve in_eq.
Hint Resolve in_cons.
Hint Extern 1 (In _ _) => compute.

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

Instance Link_equal_dec : EqualDec Link.
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



Definition example_fs := mkFS 1
  [ mkLink 1 (DirNode 2) "etc";
    mkLink 2 (FileNode 10) "passwd";
    mkLink 2 (SymlinkNode ["passwd"]) "passwd~";
    mkLink 1 (SymlinkNode ["etc"]) "etc~";
    mkLink 1 (DirNode 3) "tmp";
    mkLink 3 (SymlinkNode [".."; "etc"]) "foo";
    mkLink 3 (SymlinkNode [".."; ".."; "etc"]) "foo2";
    mkLink 3 (SymlinkNode [".."]) "root"
  ]
  [].

Theorem etc_passwd :
  path_eval_root example_fs ["etc"; "passwd"] (FileNode 10).
Proof.
  unfold path_eval_root.
  eauto 20.
Qed.

Theorem etc_passwd' :
  path_eval_root example_fs ["etc"; "passwd~"] (FileNode 10).
Proof.
  unfold path_eval_root.
  eauto 20.
Qed.

Theorem etc'_passwd :
  path_eval_root example_fs ["etc~"; "passwd"] (FileNode 10).
Proof.
  unfold path_eval_root.
  eauto 20.
Qed.

Theorem tmp_foo_passwd :
  path_eval_root example_fs ["tmp"; "foo"; "passwd"] (FileNode 10).
Proof.
  unfold path_eval_root.
  eauto 50.
Qed.

Theorem tmp_foo2_passwd :
  path_eval_root example_fs ["tmp"; "foo2"; "passwd"] (FileNode 10).
Proof.
  unfold path_eval_root.
  eauto 50.
Qed.


Hint Extern 1 False =>
  match goal with
  | H : {| LinkFrom := ?a; LinkTo := ?b; LinkName := ?c |} =
        {| LinkFrom := ?d; LinkTo := ?e; LinkName := ?f |} |- _ =>
    destruct (Link_equal_dec (mkLink a b c) (mkLink d e f)); try congruence
  end.


Theorem no_usr : ~ exists node,
  path_eval_root example_fs ["usr"] node.
Proof.
  unfold path_eval_root.
  compute.

  intro; deex.
  inversion H; clear H; subst.
  inversion H4; clear H4; subst.
  compute in *. intuition.
  compute in *. intuition.
Qed.


Definition tree_transform := Graph -> Graph.

Definition transform_fs (fs : FS) (xform : tree_transform) :=
  mkFS (FSRoot fs) (xform (FSLinks fs)) (FSFiles fs).

Definition add_link (srcdir : nat) (dst : Node) (name : string) : tree_transform :=
  fun links => mkLink srcdir dst name :: links.

Definition remove_link (srcdir : nat) (dst : Node) (name : string) : tree_transform :=
  fun links => filter (fun l => match Link_equal_dec l (mkLink srcdir dst name) with
    | left _ => false
    | right _ => true
    end) links.

Definition xform_both (x1 x2 : tree_transform) :=
  fun t => x2 (x1 t).

Notation "x1 ;; x2" := (xform_both x1 x2) (at level 50).


Record concurrent_tree_semantics := mkConcurrentSem {
  AddLinks : tree_transform;
  RemoveLinks : tree_transform;
}.

Definition apply_concurrent_adds (fs : FS) (sem : concurrent_tree_semantics) : FS :=
  transform_fs fs (AddLinks sem).

Definition apply_concurrent_all (fs : FS) (sem : concurrent_tree_semantics) : FS :=
  transform_fs fs (AddLinks sem ;; RemoveLinks sem).


Definition rename_overwrite_semantics srcdir srcname node dstdir dstname oldnode := {|
  AddLinks := add_link dstdir node dstname;
  RemoveLinks := remove_link srcdir node srcname;;
                 remove_link dstdir oldnode dstname
|}.

Definition rename_nonexist_semantics srcdir srcname node dstdir dstname := {|
  AddLinks := add_link dstdir node dstname;
  RemoveLinks := remove_link srcdir node srcname
|}.


Definition rename_example : concurrent_tree_semantics :=
  rename_nonexist_semantics 1 "tmp" (DirNode 3) 1 "tmp2".

Theorem tmp_root_tmp2_foo_passwd_concur_during :
  path_eval_root
  (apply_concurrent_adds example_fs rename_example)
  ["tmp"; "root"; "tmp2"; "foo"; "passwd"] (FileNode 10).
Proof.
  unfold path_eval_root.
  eauto 100.
Qed.

Theorem tmp_root_tmp2_foo_passwd_concur_after :
  path_eval_root
  (apply_concurrent_all example_fs rename_example)
  ["tmp2"; "foo"; "passwd"] (FileNode 10).
Proof.
  unfold path_eval_root.
  eauto 100.
Qed.

Theorem no_tmp_root_tmp2_foo_passwd_concur_after : ~ exists node,
  path_eval_root
  (apply_concurrent_all example_fs rename_example)
  ["tmp"; "root"; "tmp2"; "foo"; "passwd"] node.
Proof.
  unfold path_eval_root.
  compute.

  intro; deex.
  inversion H; clear H; subst.
  inversion H4; clear H4; subst.
  compute in *. intuition.
  compute in *. intuition.
Qed.
