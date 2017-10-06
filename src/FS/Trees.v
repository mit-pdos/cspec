Require Import String.
Require Import List.

Import ListNotations.
Open Scope string.


Inductive Node :=
| DirNode : nat -> Node
| FileNode : nat -> Node
| SymlinkNode : list string -> Node.

Record Link := mkLink {
  LinkFrom : nat;   (* Always a DirNode *)
  LinkTo : Node;
  LinkName : string
}.

Definition Graph := list Link.

Definition File := list nat.
Definition Files := list File.

Record FS := mkFS {
  FSRoot : nat;
  FSLinks : Graph;
  FSFiles : Files;
}.

Definition Pathname := list string.

Inductive valid_link : forall (g : Graph) (dir : nat) (name : string) (target : Node), Prop :=
| ValidLink : forall g dir name target,
  In (mkLink dir target name) g ->
  valid_link g dir name target
| ValidDot : forall g dir,
  valid_link g dir "." (DirNode dir)
| ValidDotDot : forall g dir name parent,
  In (mkLink parent (DirNode dir) name) g ->
  valid_link g dir ".." (DirNode parent).

Inductive path_evaluates : forall (fs : FS) (start : Node) (pn : Pathname) (target : Node), Prop :=
| PathEvalEmpty : forall fs start,
  path_evaluates fs start nil start
| PathEvalLink : forall fs startdir name namenode pn target,
  valid_link (FSLinks fs) startdir name namenode ->
  path_evaluates fs namenode pn target ->
  path_evaluates fs (DirNode startdir) (name :: pn) target
| PathEvalSymlink : forall fs startdir name sympath symtarget pn target,
  In (mkLink startdir (SymlinkNode sympath) name) (FSLinks fs) ->
  path_evaluates fs (DirNode startdir) sympath symtarget ->
  path_evaluates fs symtarget pn target ->
  path_evaluates fs (DirNode startdir) (name :: pn) target.

Definition path_eval_root (fs : FS) (pn : Pathname) (target : Node) : Prop :=
  path_evaluates fs (DirNode (FSRoot fs)) pn target.

Hint Constructors valid_link.
Hint Constructors path_evaluates.
Hint Resolve in_eq.
Hint Resolve in_cons.
Hint Extern 1 (In _ _) => compute.


Definition example_fs := mkFS 1
  [ mkLink 1 (DirNode 2) "etc";
    mkLink 2 (FileNode 10) "passwd";
    mkLink 2 (SymlinkNode ["passwd"]) "passwd~";
    mkLink 1 (SymlinkNode ["etc"]) "etc~";
    mkLink 1 (DirNode 3) "tmp";
    mkLink 3 (SymlinkNode [".."; "etc"]) "foo"
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
