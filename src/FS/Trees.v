Require Import POCS.
Require Import String.
Require Import Equalities.
Require Import MSets.MSetWeakList.

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

Inductive path_evaluates : forall (fs : FS) (start : Node) (pn : Pathname) (target : Node), Prop :=
| PathEvalEmpty : forall fs start,
  path_evaluates fs start nil start
| PathEvalLink : forall fs startdir name namenode pn target,
  valid_link fs startdir name namenode ->
  path_evaluates fs namenode pn target ->
  path_evaluates fs (DirNode startdir) (name :: pn) target
| PathEvalSymlink : forall fs startdir name sympath symtarget pn target,
  Graph.In (mkLink startdir (SymlinkNode sympath) name) (FSLinks fs) ->
  path_evaluates fs (DirNode startdir) sympath symtarget ->
  path_evaluates fs symtarget pn target ->
  path_evaluates fs (DirNode startdir) (name :: pn) target.

Definition path_eval_root (fs : FS) (pn : Pathname) (target : Node) : Prop :=
  path_evaluates fs (DirNode (FSRoot fs)) pn target.


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


(** Example valid (and some invalid) lookups *)

Definition example_fs := mkFS 1
 (Graph.add (mkLink 1 (DirNode 2) "etc")
 (Graph.add (mkLink 2 (FileNode 10) "passwd")                            
 (Graph.add (mkLink 2 (SymlinkNode ["passwd"]) "passwd~")
 (Graph.add (mkLink 1 (SymlinkNode ["etc"]) "etc~")
 (Graph.add (mkLink 1 (DirNode 3) "tmp")
 (Graph.add (mkLink 3 (SymlinkNode [".."; "etc"]) "foo")
 (Graph.add (mkLink 3 (SymlinkNode [".."; ".."; "etc"]) "foo2")
 (Graph.add (mkLink 3 (SymlinkNode [".."]) "root")
             Graph.empty))))))))
  [].

Ltac resolve_link := compute; auto 20.
Ltac resolve_name :=  eapply PathEvalLink; try constructor; resolve_link.
Ltac resolve_symname := eapply PathEvalSymlink; resolve_link.
Ltac resolve_dotdot :=  eapply PathEvalLink; try eapply ValidDotDot; resolve_link.
Ltac resolve_dotdotRoot :=  eapply PathEvalLink; try eapply ValidDotDotRoot; resolve_link.
Ltac resolve_init := left; eexists; unfold path_eval_root; split; auto.

Theorem etc_passwd :
  spec_ok example_fs (lookup_spec ["etc"; "passwd"]) (Some (FileNode 10)).
Proof.
  resolve_init.
  resolve_name.
  resolve_name.
Qed.

Theorem etc_passwd' :
  spec_ok example_fs (lookup_spec ["etc"; "passwd~"]) (Some (FileNode 10)).
Proof.
  resolve_init.
  resolve_name.
  resolve_symname.
  resolve_name.
Qed.

Theorem etc'_passwd :
  spec_ok example_fs (lookup_spec ["etc~"; "passwd"]) (Some (FileNode 10)).
Proof.
  resolve_init.
  resolve_symname.
  resolve_name.
  resolve_name.
Qed.

Theorem tmp_foo_passwd :
  spec_ok example_fs (lookup_spec ["tmp"; "foo"; "passwd"]) (Some (FileNode 10)).
Proof.
  resolve_init.
  resolve_name.
  resolve_symname.
  resolve_dotdot.
  resolve_name.
  resolve_name.
Qed.

Theorem tmp_foo2_passwd :
  spec_ok example_fs (lookup_spec ["tmp"; "foo2"; "passwd"]) (Some (FileNode 10)).
Proof.
  resolve_init.
  resolve_name.
  resolve_symname.
  resolve_dotdot.
  resolve_dotdotRoot.
  resolve_name.
  resolve_name.
Qed.


Ltac resolve_none :=
  repeat match goal with
         | H: Graph.In _ _ |- _ => apply Graph.add_spec in H; intuition idtac; try congruence
         | H: Graph.In _ Graph.empty |- _ =>  apply Graph.is_empty_spec in H; eauto
         end.

Theorem no_usr :
  spec_ok example_fs (lookup_spec ["usr"]) None.
Proof.
  simpl.
  right; eauto.
  split; eauto.
  intuition. deex.
  inversion H; clear H; subst.
  inversion H4; clear H4; subst.
  resolve_none.
  resolve_none.
Qed.


(** Example lookups (positive and negative) in the presence of a concurrent rename *)

Definition rename_example :=
  rename_nonexist_spec 1 "tmp" (DirNode 3) 1 "tmp2".

Theorem tmp_root_tmp2_foo_passwd_concur_during :
  spec_ok
    (spec_start example_fs rename_example)
    (lookup_spec ["tmp"; "root"; "tmp2"; "foo"; "passwd"])
    (Some (FileNode 10)).
Proof.
  resolve_init.

  unfold rename_example, spec_start, rename_nonexist_spec, transform_fs, add_link; simpl.
  
  (* lookup tmp, root  *)
  resolve_name.
  resolve_symname.
  resolve_dotdot; auto.

  (* finish lookup *)
  resolve_name.
  resolve_symname.
  resolve_dotdot; auto.
  resolve_name.
  resolve_name.
Qed.

Theorem tmp_root_tmp2_foo_passwd_concur_after :
  spec_ok
    (spec_finish example_fs rename_example)
    (lookup_spec ["tmp2"; "foo"; "passwd"])
    (Some (FileNode 10)).
Proof.
  resolve_init.

  unfold rename_example, spec_finish, transform_fs; simpl.
  unfold remove_link, add_link; simpl.
  
  resolve_name.
  resolve_symname.
  resolve_dotdot.
  resolve_name.
  resolve_name.
Qed.


Theorem no_tmp_root_tmp2_foo_passwd_concur_after :
  spec_ok
    (spec_finish example_fs rename_example)
    (lookup_spec ["tmp"; "root"; "tmp2"; "foo"; "passwd"])
    None.
Proof.
  simpl.
  right.
  split; auto.
  intuition. deex.
  inversion H; clear H; subst.
  inversion H4; clear H4; subst.
  
  unfold rename_example, spec_finish, transform_fs in *; simpl in *.
  unfold remove_link, add_link in *; simpl in *.

  resolve_none.

  apply Graph.remove_spec in H0; intuition idtac; try congruence.
  resolve_none.
  resolve_none.

  apply Graph.remove_spec in H; intuition idtac; try congruence.
  resolve_none.
Qed.

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
