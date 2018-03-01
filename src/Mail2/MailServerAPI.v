Require Import POCS.
Require Import String.


Module MailServerAPI <: Layer.

  Definition mbox_contents := FSet.t string.

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
  | StepDeliver : forall m mbox tid,
    xstep (Deliver m) tid
      mbox
      tt
      (FSet.add m mbox)
      nil
  | StepList : forall mbox tid r,
    FSet.is_permutation r mbox ->
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
