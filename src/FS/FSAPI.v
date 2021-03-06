Require Import CSPEC.
Require Import String.
Require Import Equalities.
Require Import MSets.MSetWeakList.
Require Import Relations.Relation_Operators.
Require Import RelationClasses.
Require Import Morphisms.
Require Import Sumbool.
Require Import FSModel.
Require Import LinkAPI.

Import ListNotations.
Open Scope string.


Notation "x <?- p1 ; p2" := (r <- p1; match r with | None => Ret None | Some x => p2 end)
  (at level 60, right associativity).


Fixpoint namei_spec (startnode : Node) (pn : Pathname) : proc _ (option Node) :=
  match pn with
  | nil =>
    Ret (Some startnode)
  | name :: pn' =>
    match startnode with
    | DirNode startdir =>
      r <- Call (LinkLookup startdir name);
      match r with
      | None => Ret None
      | Some n =>
        namei_spec n pn'
      end
    | _ => Ret None
    end
  end.

Definition namei_cwd (cwd : nat) (pn : Pathname) : proc _ (option Node) :=
  namei_spec (DirNode cwd) pn.

Definition namei_cwd_dir (cwd : nat) (pn : Pathname) : proc _ (option nat) :=
  r <?- namei_spec (DirNode cwd) pn;
  match r with
  | DirNode dirnum => Ret (Some dirnum)
  | _ => Ret None
  end.

Definition namei_cwd_file (cwd : nat) (pn : Pathname) : proc _ (option nat) :=
  r <?- namei_spec (DirNode cwd) pn;
  match r with
  | FileNode h => Ret (Some h)
  | _ => Ret None
  end.

Definition create (cwd : nat) (dir : Pathname) (name : string) :=
  dirnum <?- namei_cwd_dir cwd dir;
  Call (LinkAllocFile dirnum name).

Definition mkdir (cwd : nat) (dir : Pathname) (name : string) :=
  dirnum <?- namei_cwd_dir cwd dir;
  Call (LinkAllocDir dirnum name).

Definition unlink (cwd : nat) (dir : Pathname) (name : string) :=
  dirnum <?- namei_cwd_dir cwd dir;
  n <?- Call (LinkLookup dirnum name);
  _ <- Call (LinkDel dirnum name n);
  Ret (Some tt).

Definition stat (cwd : nat) (dir : Pathname) (name : string) :=
  dirnum <?- namei_cwd_dir cwd dir;
  n <?- Call (LinkLookup dirnum name);
  match n with
  | FileNode _ => Ret (Some StatFile)
  | DirNode _ => Ret (Some StatDir)
  end.

Definition readdir (cwd : nat) (pn : Pathname) :=
  dirnum <?- namei_cwd_dir cwd pn;
  Call (LinkList dirnum).

Definition rename (cwd : nat) (srcdir : Pathname) (srcname : string)
                              (dstdir : Pathname) (dstname : string) :=
  srcdirnum <?- namei_cwd_dir cwd srcdir;
  dstdirnum <?- namei_cwd_dir cwd dstdir;
  srcnode <?- Call (LinkLookup srcdirnum srcname);
  dstnodeopt <- Call (LinkLookup dstdirnum dstname);
  match srcnode with
  | FileNode _ =>
    match dstnodeopt with
    | None =>
      _ <- Call (LinkAdd dstdirnum dstname srcnode);
      _ <- Call (LinkDel srcdirnum srcname srcnode);
      Ret (Some tt)
    | Some (FileNode dstfile) =>
      _ <- Call (LinkAdd dstdirnum dstname srcnode);
      _ <- Call (LinkDel dstdirnum dstname (FileNode dstfile));
      _ <- Call (LinkDel srcdirnum srcname srcnode);
      Ret (Some tt)
    | _ =>
      Ret None
    end
  | _ => Ret None
  end.

Definition find_available_name (cwd : nat) (pn : Pathname) (pfx : string) :=
  dirnum <?- namei_cwd_dir cwd pn;
  name <- Call (LinkFindUnusedName dirnum pfx);
  Ret (Some name).

Definition read (cwd : nat) (pn : Pathname) :=
  f <?- namei_cwd_file cwd pn;
  d <- Call (FileRead f);
  Ret (Some d).

Definition write (cwd : nat) (pn : Pathname) (data : string) :=
  f <?- namei_cwd_file cwd pn;
  _ <- Call (FileWrite f data);
  Ret (Some tt).
