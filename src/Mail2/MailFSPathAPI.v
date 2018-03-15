Require Import POCS.
Require Import String.
Require Import MailServerAPI.
Require Import MailFSPathAbsAPI.


Module MailFSPathAPI <: Layer.

  Import MailServerAPI.
  Import MailFSPathAbsAPI.

  Inductive xopT : Type -> Type :=
  | CreateWrite : forall (tmpfn : string * string) (data : string), xopT unit
  | Link : forall (tmpfn : string * string) (mboxfn : string * string), xopT unit
  | Unlink : forall (tmpfn : string * string), xopT unit

  | GetTID : xopT nat
  | Random : xopT nat

  | List : forall (dir : string), xopT (list string)
  | Read : forall (fn : string * string), xopT string
  | GetRequest : xopT request
  | Respond : forall (T : Type) (v : T), xopT unit
  .

  Definition opT := xopT.
  Definition State := MailFSPathAbsAPI.State.
  Definition initP (s : State) := True.

  Inductive xstep : forall T, opT T -> nat -> State -> T -> State -> list event -> Prop :=
  | StepCreateWrite : forall fs tid tmpfn data,
    xstep (CreateWrite tmpfn data) tid
      fs
      tt
      (FMap.add tmpfn data fs)
      nil
  | StepUnlink : forall fs tid tmpfn,
    xstep (Unlink tmpfn) tid
      fs
      tt
      (FMap.remove tmpfn fs)
      nil
  | StepLink : forall fs tid mailfn data tmpfn,
    FMap.MapsTo tmpfn data fs ->
    xstep (Link tmpfn mailfn) tid
      fs
      tt
      (FMap.add mailfn data fs)
      nil

  | StepList : forall fs tid r dirname,
    FMap.is_permutation_key r (drop_dirname (filter_dir dirname fs)) ->
    xstep (List dirname) tid
      fs
      r
      fs
      nil

  | StepGetTID : forall fs tid,
    xstep GetTID tid
      fs
      tid
      fs
      nil
  | StepRandom : forall fs tid r,
    xstep Random tid
      fs
      r
      fs
      nil

  | StepRead : forall fn fs tid m,
    FMap.MapsTo fn m fs ->
    xstep (Read fn) tid
      fs
      m
      fs
      nil
  | StepGetRequest : forall s tid r,
    xstep GetRequest tid
      s
      r
      s
      (Event r :: nil)
  | StepRespond : forall s tid T (v : T),
    xstep (Respond v) tid
      s
      tt
      s
      (Event v :: nil)
  .

  Definition step := xstep.

End MailFSPathAPI.
