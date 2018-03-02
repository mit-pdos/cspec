Require Import POCS.
Require Import String.
Require Import MailServerAPI.
Require Import MailServerDirAPI.


Module MailboxAPI <: Layer.

  Import MailServerAPI.
  Import MailServerDirAPI.

  Inductive xopT : Type -> Type :=
  | Deliver : forall (m : string), xopT unit
  | List : xopT (list (nat*nat))
  | Read : forall (fn : nat*nat), xopT string
  | GetRequest : xopT request
  | Respond : forall (T : Type) (v : T), xopT unit
  .

  Definition opT := xopT.
  Definition State := dir_contents.
  Definition initP (s : State) := True.

  Inductive xstep : forall T, opT T -> nat -> State -> T -> State -> list event -> Prop :=
  | StepDeliver : forall m mbox tid fn,
    ~ FMap.In fn mbox ->
    xstep (Deliver m) tid
      mbox
      tt
      (FMap.add fn m mbox)
      nil
  | StepList : forall mbox tid r,
    FMap.is_permutation_key r mbox ->
    xstep List tid
      mbox
      r
      mbox
      nil
  | StepRead : forall fn mbox tid m,
    FMap.MapsTo fn m mbox ->
    xstep (Read fn) tid
      mbox
      m
      mbox
      nil
  | StepGetRequest : forall mbox tid r,
    xstep GetRequest tid
      mbox
      r
      mbox
      (Event r :: nil)
  | StepRespond : forall mbox tid T (v : T),
    xstep (Respond v) tid
      mbox
      tt
      mbox
      (Event v :: nil)
  .

  Definition step := xstep.

End MailboxAPI.
