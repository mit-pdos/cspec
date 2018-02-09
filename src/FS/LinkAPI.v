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
| LinkFindUnusedName (dir : nat) (prefix : string) : linkOpT string
| FileRead (f : nat) : linkOpT string
| FileWrite (f : nat) (data : string) : linkOpT unit
| GetTID : linkOpT nat.


Inductive stat_result :=
| StatFile
| StatDir.


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
  | StepGetRoot : forall tid fs r,
    r = FSRoot fs ->
    xstep LinkGetRoot tid
      fs
      r
      fs
  | StepFindUnusedName : forall tid fs dir pfx name,
    prefix pfx name = true ->
    (~ exists target, valid_link fs dir name target) ->
    xstep (LinkFindUnusedName dir pfx) tid
      fs
      name
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

  Definition initP (_ : State) := True.

End LinkAPI.
