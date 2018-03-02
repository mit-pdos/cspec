Require Import POCS.
Require Import String.
Require Import MailServerAPI.


Module MailServerDirAPI <: Layer.

  Import MailServerAPI.

  Definition dir_contents := FMap.t (nat*nat) string.

  Definition opT := MailServerAPI.opT.
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
    FMap.is_permutation_val r mbox ->
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

End MailServerDirAPI.
