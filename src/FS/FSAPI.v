Require Import POCS.
Require Import String.
Require Import Equalities.
Require Import MSets.MSetWeakList.
Require Import Relations.Relation_Operators.
Require Import RelationClasses.
Require Import Morphisms.
Require Import Sumbool.
Require Import FSModel.

Import ListNotations.
Open Scope string.


(** Opcodes *)

Inductive linkOpT : Type -> Type :=
| LinkAdd (dir : nat) (name : string) (target : Node) : linkOpT bool
| LinkAllocFile (dir : nat) (name : string) : linkOpT (option nat)
| LinkAllocDir (dir : nat) (name : string) : linkOpT (option nat)
| LinkDel (dir : nat) (name : string) (target : Node) : linkOpT bool
| LinkLookup (dir : nat) (name : string) : linkOpT (option Node)
| LinkList (dir : nat) : linkOpT (option (list string))
| LinkGetRoot : linkOpT nat
| FileRead (f : nat) : linkOpT string
| FileWrite (f : nat) (data : string) : linkOpT unit
| GetTID : linkOpT nat.


Inductive stat_result :=
| StatFile
| StatDir.

Inductive fsOpT : Type -> Type :=
| Create (cwd : nat) (dir : Pathname) (name : string) : fsOpT nat
| Mkdir (cwd : nat) (dir : Pathname) (name : string) : fsOpT nat
| Unlink (cwd : nat) (dir : Pathname) (name : string) : fsOpT unit
| Stat (cwd : nat) (dir : Pathname) (name : string) : fsOpT (option stat_result)
| Readdir (cwd : nat) (pn : Pathname) : fsOpT (list string)
| Rename (cwd : nat) (src : Pathname) (dstdir : Pathname) (dstname : string) : fsOpT unit
| Read (cwd : nat) (pn : Pathname) : fsOpT string
| Write (cwd : nat) (pn : Pathname) (data : string) : fsOpT unit
| FindAvailableName (cwd : nat) (dir : Pathname) : fsOpT string
| Debug (s : string) : fsOpT unit.


Module LinkAPI <: Layer.

  Definition opT := linkOpT.
  Definition State := FS.

  Inductive xstep : forall T, opT T -> nat -> State -> T -> State -> Prop :=
  | StepAdd : forall dir name target tid fs,
    xstep (LinkAdd dir name target) tid
      fs
      true
      (add_link dir target name fs)
  | StepAllocFile : forall dir name fid tid fs,
    file_handle_valid fs fid ->
    file_handle_unused fs fid ->
    xstep (LinkAllocFile dir name) tid
      fs
      (Some fid)
      (add_link dir (FileNode fid) name fs)
  | StepAllocDir : forall dir name did tid fs,
    (~ exists pn, path_eval_root fs pn (DirNode did)) ->
    xstep (LinkAllocDir dir name) tid
      fs
      (Some did)
      (add_link dir (DirNode did) name fs)
  | StepDel : forall dir name target tid fs,
    xstep (LinkDel dir name target) tid
      fs
      true
      (del_link dir target name fs)
  | StepLookupAbsent : forall dir name tid fs,
    (~ exists target, valid_link fs dir name target) ->
    xstep (LinkLookup dir name) tid
      fs
      None
      fs
  | StepLookupFound : forall dir name target tid fs,
    valid_link fs dir name target ->
    xstep (LinkLookup dir name) tid
      fs
      (Some target)
      fs
  | StepList : forall dir tid fs,
    xstep (LinkList dir) tid
      fs
      (Some (readdir_names fs dir))
      fs
  | StepGetRoot : forall tid fs,
    xstep LinkGetRoot tid
      fs
      (FSRoot fs)
      fs
  | StepRead : forall f data tid fs,
    nth_error (FSFiles fs) f = Some data ->
    xstep (FileRead f) tid
      fs
      data
      fs
  | StepWrite : forall f data tid fs,
    xstep (FileWrite f data) tid
      fs
      tt
      (upd_file f data fs)
  | StepGetTID : forall tid fs,
    xstep GetTID tid
      fs
      tid
      fs.

  Definition step := xstep.

End LinkAPI.


Notation "x <?- p1 ; p2" := (r <- p1; match r with | None => Ret None | Some x => p2 end)
  (at level 60, right associativity).


Fixpoint namei_spec (nstep : nat) (startnode : Node) (pn : Pathname) : proc _ (option Node) :=
  match nstep with
  | O => Ret None
  | S nstep' =>
    match pn with
    | nil =>
      Ret (Some startnode)
    | name :: pn' =>
      match startnode with
      | DirNode startdir =>
        r <- Op (LinkLookup startdir name);
        match r with
        | None => Ret None
        | Some (SymlinkNode sympath) =>
          osymnode <- namei_spec nstep' startnode sympath;
          match osymnode with
          | None => Ret None
          | Some symnode =>
            namei_spec nstep' symnode pn'
          end
        | Some n =>
          namei_spec nstep' n pn'
        end
      | _ => Ret None
      end
    end
  end.

Definition namei_cwd (cwd : nat) (pn : Pathname) : proc _ (option Node) :=
  namei_spec 100 (DirNode cwd) pn.

Definition namei_cwd_dir (cwd : nat) (pn : Pathname) : proc _ (option nat) :=
  r <?- namei_spec 100 (DirNode cwd) pn;
  match r with
  | DirNode dirnum => Ret (Some dirnum)
  | _ => Ret None
  end.

Definition namei_cwd_file (cwd : nat) (pn : Pathname) : proc _ (option nat) :=
  r <?- namei_spec 100 (DirNode cwd) pn;
  match r with
  | FileNode h => Ret (Some h)
  | _ => Ret None
  end.

Definition create (cwd : nat) (dir : Pathname) (name : string) :=
  dirnum <?- namei_cwd_dir cwd dir;
  Op (LinkAllocFile dirnum name).

Definition mkdir (cwd : nat) (dir : Pathname) (name : string) :=
  dirnum <?- namei_cwd_dir cwd dir;
  Op (LinkAllocDir dirnum name).

Definition unlink (cwd : nat) (dir : Pathname) (name : string) :=
  dirnum <?- namei_cwd_dir cwd dir;
  n <?- Op (LinkLookup dirnum name);
  _ <- Op (LinkDel dirnum name n);
  Ret (Some tt).

Definition stat (cwd : nat) (dir : Pathname) (name : string) :=
  dirnum <?- namei_cwd_dir cwd dir;
  n <?- Op (LinkLookup dirnum name);
  match n with
  | FileNode _ => Ret (Some StatFile)
  | DirNode _ => Ret (Some StatDir)
  | _ => Ret None
  end.

Definition readdir (cwd : nat) (pn : Pathname) :=
  dirnum <?- namei_cwd_dir cwd pn;
  Op (LinkList dirnum).

Definition rename (cwd : nat) (srcdir : Pathname) (srcname : string)
                              (dstdir : Pathname) (dstname : string) :=
  srcdirnum <?- namei_cwd_dir cwd srcdir;
  dstdirnum <?- namei_cwd_dir cwd dstdir;
  srcnode <?- Op (LinkLookup srcdirnum srcname);
  dstnodeopt <- Op (LinkLookup dstdirnum dstname);
  match srcnode with
  | FileNode _ =>
    match dstnodeopt with
    | None =>
      _ <- Op (LinkAdd dstdirnum dstname srcnode);
      _ <- Op (LinkDel srcdirnum srcname srcnode);
      Ret (Some tt)
    | Some (FileNode dstfile) =>
      _ <- Op (LinkAdd dstdirnum dstname srcnode);
      _ <- Op (LinkDel dstdirnum dstname (FileNode dstfile));
      _ <- Op (LinkDel srcdirnum srcname srcnode);
      Ret (Some tt)
    | _ =>
      Ret None
    end
  | _ => Ret None
  end.

Definition read (cwd : nat) (pn : Pathname) :=
  f <?- namei_cwd_file cwd pn;
  d <- Op (FileRead f);
  Ret (Some d).

Definition write (cwd : nat) (pn : Pathname) (data : string) :=
  f <?- namei_cwd_file cwd pn;
  _ <- Op (FileWrite f data);
  Ret (Some tt).
