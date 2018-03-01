Require Import POCS.
Require Import FMapInterface.
Require Import FMapAVL.
Require Import String.


Module MailServerAPI <: Layer.

  Module Dir := FMapAVL.Make(String_as_OT).

  Definition mbox_contents := Dir.t string.

  Inductive request :=
  | ReqDeliver (msg : string)
  | ReqRead
  .

  Inductive xopT : Type -> Type :=
  | Deliver : forall (m : string), xopT unit
  | ReadAll : xopT (list string)
  | GetRequest : xopT request
  | Respond : forall (T : Type) (v : T), xopT unit
  .

  Definition opT := xopT.
  Definition State := mbox_contents.
  Definition initP (s : State) := True.

  Inductive xstep : forall T, opT T -> nat -> State -> T -> State -> list event -> Prop :=
  | StepDeliver : forall m mbox tid fn,
    ~ Dir.In fn mbox ->
    xstep (Deliver m) tid
      mbox
      tt
      (Dir.add fn m mbox)
      nil
  | StepList : forall mbox tid r,
    r = map snd (Dir.elements mbox) ->
    xstep ReadAll tid
      mbox
      r
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

End MailServerAPI.
