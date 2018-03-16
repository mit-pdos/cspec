Require Import POCS.
Require Import String.


Module MailServerAPI <: Layer.

  Definition dir_contents := FMap.t (nat*nat) string.

  Inductive request :=
  | ReqDeliver (msg : string)
  | ReqRead
  .

  Inductive xopT : Type -> Type :=
  | Deliver : forall (m : string), xopT unit
  | Pickup : xopT (list ((nat*nat) * string))
  | Delete : forall (id : nat*nat), xopT unit
  | GetRequest : xopT request
  | Respond : forall (T : Type) (v : T), xopT unit
  .

  Definition opT := xopT.
  Definition State := dir_contents.
  Definition initP (s : State) := True.

  Inductive xstep : forall T, opT T -> nat -> State -> T -> State -> list event -> Prop :=
  | StepDeliver : forall m mbox fn tid,
    ~ FMap.In fn mbox ->
    xstep (Deliver m) tid
      mbox
      tt
      (FMap.add fn m mbox)
      nil
  | StepPickup : forall mbox tid r,
    FMap.is_permutation_kv r mbox ->
    xstep Pickup tid
      mbox
      r
      mbox
      nil
  | StepDelete : forall mbox tid id,
    xstep (Delete id) tid
      mbox
      tt
      (FMap.remove id mbox)
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
