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

Definition t := Graph.singleton (mkLink 0 (FileNode 0) "x").

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


(** Largely boilerplate helpers and proof hints *)

Hint Constructors valid_link.
Hint Constructors path_evaluates.

Hint Extern 1 False =>
  match goal with
  | H : {| LinkFrom := ?a; LinkTo := ?b; LinkName := ?c |} =
        {| LinkFrom := ?d; LinkTo := ?e; LinkName := ?f |} |- _ =>
    destruct (Graph.eq_dec (mkLink a b c) (mkLink d e f)); congruence
  end.

(** Definition of concurrent tree modifications, to write specifications *)

Definition tree_transform := Graph.t -> Graph.t.

Definition transform_fs (fs : FS) (xform : tree_transform) :=
  mkFS (FSRoot fs) (xform (FSLinks fs)) (FSFiles fs).

Definition add_link (srcdir : nat) (dst : Node) (name : string) : tree_transform :=
  fun links => Graph.add (mkLink srcdir dst name) links.

Definition remove_link (srcdir : nat) (dst : Node) (name : string) : tree_transform :=
  fun links => Graph.remove (mkLink srcdir dst name) links.

Definition xform_both (x1 x2 : tree_transform) :=
  fun t => x2 (x1 t).

Definition xform_id : tree_transform :=
  fun t => t.

Notation "x1 ;; x2" := (xform_both x1 x2) (at level 50).

(** This is what a specification looks like *)

Record specification (R : Type) := mkSpec {
  Result : forall (result : R) (fs : FS), Prop;
  AddLinks : tree_transform;
  RemoveLinks : tree_transform;
}.

Definition spec_start {R} (fs : FS) (spec : specification R) : FS :=
  transform_fs fs (AddLinks spec).

Definition spec_finish {R} (fs : FS) (spec : specification R) : FS :=
  transform_fs fs (RemoveLinks spec ;; AddLinks spec).

Definition spec_ok {R} (fs : FS) (spec : specification R) (r : R) : Prop :=
  Result spec r fs.


(** Concrete specifications *)

Definition lookup_spec (pn : Pathname) : specification (option Node) := {|
  Result := fun result fs =>
    (exists node, result = Some node /\ path_eval_root fs pn node) \/
    result = None /\ ~ exists node, path_eval_root fs pn node;
  AddLinks := xform_id;
  RemoveLinks := xform_id;
|}.

Definition rename_overwrite_spec srcdir srcname node dstdir dstname oldnode := {|
  Result := fun r _ => r = tt;
  AddLinks := add_link dstdir node dstname;
  RemoveLinks := remove_link srcdir node srcname;;
                 remove_link dstdir oldnode dstname
|}.

Definition rename_nonexist_spec srcdir srcname node dstdir dstname := {|
  Result := fun r _ => r = tt;
  AddLinks := add_link dstdir node dstname;
  RemoveLinks := remove_link srcdir node srcname
|}.

(**
  TODO: take just Pathname arguments, rather than relying on knowing
  node (and oldnode, if exists) already.

  tricky issues:
  - moving a symlink: need to move the SymlinkNode, not the evaluated target.
  - overwriting a symlink?
  - what if there are multiple possibilities for a given name?
    saying "~ exists .., path_eval_root" seems to imply NONE of
    these concurrent syscalls can be running now.
 *)

(*
Definition rename_spec srcdir srcname dstdir dstname := {|
  Result := fun r _ =>
    r = true <-> exists n, path_eval_root fs (srcdir ++ [srcname]) n /\
      ~ exists d, path_eval_root fs (dstdir ++ [dstname]) (DirNode d);
  AddLinks := add_link 
|}.
*)

Definition names := list string.

Definition dirents dirnum (g: Graph.t) :=
  Graph.filter (fun (l: Link) => (beq_nat (LinkFrom l) dirnum)) g.

Definition dirnames dirnum g : names :=
  let dir := dirents dirnum g in
  map (fun (l:Link) => (LinkName l)) (Graph.elements dir).

Definition readdir_spec pn : specification (option names)  := {|
  Result := fun result fs =>
              (exists node dir n, dir = Some (DirNode n) /\ path_eval_root fs pn node /\
                           result = Some (dirnames n (FSLinks fs))
              ) \/
              result = None /\  ~ exists node n, path_eval_root fs pn node /\ node = (DirNode n);
  AddLinks := xform_id;
  RemoveLinks := xform_id;
|}.

