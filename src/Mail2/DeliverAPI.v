Require Import POCS.
Require Import String.


Module MailboxAPI <: Layer.

  Definition dir_contents := FMap.t (nat*string) string.

  Inductive mbox_opT : Type -> Type :=
  | Deliver : forall (m : string), mbox_opT unit
  .

  Definition opT := mbox_opT.
  Record state_rec := mk_state {
    tmpdir : dir_contents;
    maildir : dir_contents;
  }.
  Definition State := state_rec.
  Definition initP (s : State) := True.

  Inductive xstep : forall T, opT T -> nat -> State -> T -> State -> list event -> Prop :=
  | StepDeliver : forall m tmp mbox tid fn,
    ~ FMap.In fn mbox ->
    xstep (Deliver m) tid
      (mk_state tmp mbox)
      tt
      (mk_state tmp (FMap.add fn m mbox))
      nil
  .

  Definition step := xstep.

End MailboxAPI.


Module TmpdirAPI <: Layer.

  Import MailboxAPI.

  Inductive tmpdir_opT : Type -> Type :=
  | CreateTmp : forall (data : string), tmpdir_opT string
  | LinkMail : forall (fn : string), tmpdir_opT unit
  | UnlinkTmp : forall (fn : string), tmpdir_opT unit
  .

  Definition opT := tmpdir_opT.
  Definition State := MailboxAPI.State.
  Definition initP (s : State) := True.

  Inductive xstep : forall T, opT T -> nat -> State -> T -> State -> list event -> Prop :=
  | StepCreateTmp : forall m tmp mbox tid fn,
    ~ FMap.In (tid, fn) tmp ->
    xstep (CreateTmp m) tid
      (mk_state tmp mbox)
      fn
      (mk_state (FMap.add (tid, fn) m tmp) mbox)
      nil
  | StepUnlinkTmp : forall tmp mbox tid fn,
    xstep (UnlinkTmp fn) tid
      (mk_state tmp mbox)
      tt
      (mk_state (FMap.remove (tid, fn) tmp) mbox)
      nil
  | StepLinkMail : forall tmp mbox tid tmpfn mailfn data,
    FMap.MapsTo (tid, tmpfn) data tmp ->
    ~ FMap.In (tid, mailfn) mbox ->
    xstep (LinkMail tmpfn) tid
      (mk_state tmp mbox)
      tt
      (mk_state tmp (FMap.add (tid, mailfn) data mbox))
      nil
  .

  Definition step := xstep.

End TmpdirAPI.
