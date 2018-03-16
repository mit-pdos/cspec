Require Import POCS.
Require Import String.
Require Import MailboxAPI.
Require Import MailServerAPI.


Module MailboxTmpAbsAPI <: Layer.

  Import MailboxAPI.

  Definition opT := xopT.

  Record state_rec := mk_state {
    tmpdir : MailServerAPI.dir_contents;
    maildir : MailServerAPI.dir_contents;
  }.

  Definition State := state_rec.
  Definition initP (s : State) := True.

  Inductive xstep : forall T, opT T -> nat -> State -> T -> State -> list event -> Prop :=
  | StepDeliver : forall m tmp tmp' mbox tid fn,
    ~ FMap.In fn mbox ->
    xstep (Deliver m) tid
      (mk_state tmp mbox)
      tt
      (mk_state tmp' (FMap.add fn m mbox))
      nil
  | StepList : forall tmp mbox tid r,
    FMap.is_permutation_key r mbox ->
    xstep List tid
      (mk_state tmp mbox)
      r
      (mk_state tmp mbox)
      nil
  | StepReadOK : forall fn tmp mbox tid m,
    FMap.MapsTo fn m mbox ->
    xstep (Read fn) tid
      (mk_state tmp mbox)
      (Some m)
      (mk_state tmp mbox)
      nil
  | StepReadNone : forall fn tmp mbox tid,
    ~ FMap.In fn mbox ->
    xstep (Read fn) tid
      (mk_state tmp mbox)
      None
      (mk_state tmp mbox)
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

End MailboxTmpAbsAPI.
