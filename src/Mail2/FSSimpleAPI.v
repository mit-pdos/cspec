Require Import POCS.
Require Import String.
Require Import MailServerAPI.
Require Import MailServerDirAPI.
Require Import MailFSAPI.

Import ListNotations.
Open Scope string.

Module FSSimpleAPI <: Layer.

  Import MailServerAPI.

  Inductive xopT : Type -> Type :=
  | Create : forall (p : string), xopT string
  | Write : forall (p : string) (data : string), xopT unit
  | Link : forall (src : string) (dst : string), xopT unit
  | Unlink : forall (p : string), xopT unit

  | GetTID : xopT nat
  | List : forall (p: string), xopT (list (nat * string))
  | Read : forall (fn : string), xopT string
  | GetRequest : xopT request
  | Respond : forall (T : Type) (v : T), xopT unit
  .

  Definition opT := xopT.
  Definition fs_contents := FMap.t (string * (nat*string)) string.
  Definition State := fs_contents.
  Definition initP (s : State) := True.

  Parameter listdir: string -> fs_contents -> (list (N * string)).
                     
  Inductive xstep : forall T, opT T -> nat -> State -> T -> State -> list event -> Prop :=
  | StepCreate : forall state tid dir fn,
    ~ FMap.In (dir, (tid, fn)) state ->
    xstep (Create (dir++fn)) tid
      state
      fn
      (FMap.add (dir, (tid, fn)) "" state)
      nil
  | StepWrite : forall state dir tid fn data,
    FMap.In (dir, (tid, fn)) state ->
    xstep (Write (dir++fn) data) tid
      state
      tt
      (FMap.add (dir, (tid, fn)) data state)
      nil
  | StepUnlink: forall state dir tid fn,
    xstep (Unlink fn) tid
      state
      tt
      (FMap.remove (dir, (tid, fn)) state)
      nil
  | StepLink: forall state dir1 dir2 tid tmpfn mailfn data,
    FMap.MapsTo (dir1, (tid, tmpfn)) data state ->
    ~ FMap.In (dir2, (tid, mailfn)) state ->
    xstep (Link (dir1++tmpfn) (dir2++mailfn)) tid
      state
      tt
      (FMap.add (dir2, (tid, mailfn)) data state)
      nil
  | StepList : forall dir state tid r,
    (* FMap.is_permutation_key r (listdir dir state) -> *)
    xstep (List dir) tid
      state
      r
      state
      nil
  | StepGetTID : forall state tid,
    xstep GetTID tid
      state
      tid
      state
      nil

  | StepRead : forall dir fn state tid m,
    FMap.MapsTo (dir, (tid, fn)) m state ->
    xstep (Read (dir++fn)) tid
      state
      m
      state
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

End FSSimpleAPI.