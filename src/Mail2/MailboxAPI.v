Require Import POCS.
Require Import FMapInterface.
Require Import FMapAVL.
Require Import String.


Module MailboxAPI <: Layer.

  Module Dir := FMapAVL.Make(String_as_OT).

  Definition mbox_contents := Dir.t string.

  Inductive mbox_opT : Type -> Type :=
  | Deliver : forall (m : string), mbox_opT unit
  | List : mbox_opT (list string)
  | Read : forall (fn : string), mbox_opT string
  .

  Definition opT := mbox_opT.
  Definition State := mbox_contents.
  Definition initP (s : State) := True.

  Inductive xstep : forall T, opT T -> nat -> State -> T -> State -> Prop :=
  | StepDeliver : forall m mbox tid fn,
    ~ Dir.In fn mbox ->
    xstep (Deliver m) tid
      mbox
      tt
      (Dir.add fn m mbox)
  | StepList : forall mbox tid,
    xstep List tid
      mbox
      (map fst (Dir.elements mbox))
      mbox
  | StepRead : forall fn mbox tid m,
    Dir.MapsTo fn m mbox ->
    xstep (Read fn) tid
      mbox
      m
      mbox
  .

  Definition step := xstep.

End MailboxAPI.


Module AtomicMailboxAPI <: Layer.

  Module Dir := MailboxAPI.Dir.

  Inductive atomic_mbox_opT : Type -> Type :=
  | Deliver : forall (m : string), atomic_mbox_opT unit
  | ReadAll : atomic_mbox_opT (list string)
  .

  Definition opT := atomic_mbox_opT.
  Definition State := MailboxAPI.State.
  Definition initP (s : State) := True.

  Inductive xstep : forall T, opT T -> nat -> State -> T -> State -> Prop :=
  | StepDeliver : forall m mbox tid fn,
    ~ Dir.In fn mbox ->
    xstep (Deliver m) tid
      mbox
      tt
      (Dir.add fn m mbox)
  | StepList : forall mbox tid r,
    r = map snd (Dir.elements mbox) ->
    xstep ReadAll tid
      mbox
      r
      mbox
  .

  Definition step := xstep.

End AtomicMailboxAPI.
