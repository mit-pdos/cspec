Require Import POCS.
Require Import Relations.Relation_Operators.
Require Import RelationClasses.
Require Import Morphisms.

Import ListNotations.
Require Import String.
Require Import Trees.

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

Ltac resolve_link := constructor; compute; auto 20.
Ltac resolve_filename :=  apply PathEvalFileLink; resolve_link.
Ltac resolve_dirname :=  eapply PathEvalDirLink; [ resolve_link |].
Ltac resolve_fsymname := eapply PathEvalSymlink; [ resolve_link | resolve_filename; auto | auto].
Ltac resolve_dsymname := eapply PathEvalSymlink; [ resolve_link | resolve_dirname; auto | auto].
Ltac resolve_dotdot := eapply PathEvalDirLink; [ eapply ValidDotDot; compute; auto | ].
Ltac resolve_dotdotRoot :=  eapply PathEvalDirLink; [ eapply ValidDotDotRoot; compute; auto| ].
Ltac resolve_init := left; eexists; unfold path_eval_root; split; auto.

Theorem etc_passwd :
  spec_ok example_fs (lookup_spec ["etc"; "passwd"]) (Some (FileNode 10)).
Proof.
  resolve_init.
  resolve_dirname.
  resolve_filename.
Qed.

Theorem etc_passwd' :
  spec_ok example_fs (lookup_spec ["etc"; "passwd~"]) (Some (FileNode 10)).
Proof.
  resolve_init.
  resolve_dirname.
  resolve_fsymname.
Qed.

Theorem etc'_passwd :
  spec_ok example_fs (lookup_spec ["etc~"; "passwd"]) (Some (FileNode 10)).
Proof.
  resolve_init.
  resolve_dsymname.
  resolve_filename.
Qed.

Theorem tmp_foo_passwd :
  spec_ok example_fs (lookup_spec ["tmp"; "foo"; "passwd"]) (Some (FileNode 10)).
Proof.
  resolve_init.
  resolve_dirname.
  
  eapply PathEvalSymlink.
  resolve_link.
 
  resolve_dotdot.
  
  resolve_dirname; auto.
  resolve_filename.
Qed.

Theorem tmp_foo2_passwd :
  spec_ok example_fs (lookup_spec ["tmp"; "foo2"; "passwd"]) (Some (FileNode 10)).
Proof.
  resolve_init.
  resolve_dirname.

  eapply PathEvalSymlink.
  resolve_link.
 
  resolve_dotdot.
  2: resolve_filename.
  resolve_dotdotRoot.
  resolve_dirname.
  auto.
Qed.

Ltac resolve_none :=
  repeat match goal with
         | H: Graph.In _ _ |- _ => apply Graph.add_spec in H; intuition idtac; try congruence
         | H: Graph.In _ Graph.empty |- _ =>  apply Graph.is_empty_spec in H; eauto
         end.

Ltac resolve_none' :=
  repeat match goal with
         | H: Graph.In  _ _ |- _ => inversion H; subst; clear H
         | H: _ = _ |- _ => inversion H; subst; clear H
         | H: SetoidList.InA eq _ _ |- _ => inversion H; subst; clear H
         end.

Theorem no_usr :
  spec_ok example_fs (lookup_spec ["usr"]) None.
Proof.
  simpl.
  right; eauto.
  split; eauto.
  intuition. deex.
  inversion H; clear H; subst.
  inversion H3; clear H3; subst.
  resolve_none.
  inversion H4; subst.
  resolve_none.
  inversion H4; subst.
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
  resolve_dirname.
  
  eapply PathEvalSymlink.
  resolve_link.
  resolve_dotdot; auto.

  (* finish lookup *)
  resolve_dirname.

  eapply PathEvalSymlink.
  resolve_link.
  resolve_dotdot; auto.
  resolve_dirname; auto.
  resolve_filename.
Qed.

Theorem tmp_root_tmp2_foo_passwd_concur_after :
  spec_ok
    (spec_finish example_fs rename_example)
    (lookup_spec ["tmp2"; "foo"; "passwd"])
    (Some (FileNode 10)).
Proof.
  resolve_init.

  unfold rename_example, spec_finish, transform_fs; simpl.
  unfold remove_link, add_link;
    
  resolve_dirname.
  eapply PathEvalSymlink.
  resolve_link.
  resolve_dotdot. auto.
  2: resolve_dirname; auto.
  2: resolve_filename; auto.
  Unshelve.
  2: exact "tmp2".
  compute. auto 20.
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
  unfold rename_example, spec_finish, transform_fs, rename_nonexist_spec in *.
  intuition. deex.
  inversion H; clear H; subst.
  inversion H4; clear H4; subst.

  resolve_none.
  apply Graph.remove_spec in H0; intuition idtac; try congruence.
  resolve_none.
  resolve_none.

  inversion H4; subst; clear H4.
  resolve_none.
  apply Graph.remove_spec in H0.
  intuition idtac; try congruence.
  
  inversion H5; subst; clear H5.
  all: resolve_none'.
Qed.


