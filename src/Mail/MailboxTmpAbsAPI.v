Require Import CSPEC.
Require Import MailboxAPI.
Require Import MailServerAPI.

Module MailboxTmpAbsState <: State.

  Record state_rec := mk_state {
    tmpdir : MailServerState.dir_contents;
    maildir : MailServerState.dir_contents;
    locked : bool;
  }.

  Definition State := state_rec.
  Definition initP (s : State) := locked s = false /\
                              tmpdir s = FMap.empty /\
                              maildir s = FMap.empty.

End MailboxTmpAbsState.
Module MailboxTmpAbsHState := HState MailboxTmpAbsState UserIdx.


Module MailboxTmpAbsAPI <: Layer MailboxOp MailboxTmpAbsState.

  Import MailboxOp.
  Import MailboxTmpAbsState.


  Inductive xstep : forall T, Op T -> nat -> State -> T -> State -> list event -> Prop :=
  | StepDeliverOK : forall m tmp tmp' mbox tid fn lock,
    ~ FMap.In fn mbox ->
    xstep (Deliver m) tid
      (mk_state tmp mbox lock)
      true
      (mk_state tmp' (FMap.add fn m mbox) lock)
      nil
  | StepDeliverErr : forall m tmp tmp' mbox tid lock,
    xstep (Deliver m) tid
      (mk_state tmp mbox lock)
      false
      (mk_state tmp' mbox lock)
      nil
  | StepList : forall tmp mbox tid r lock,
    FMap.is_permutation_key r mbox ->
    xstep List tid
      (mk_state tmp mbox lock)
      r
      (mk_state tmp mbox lock)
      nil
  | StepReadOK : forall fn tmp mbox tid m lock,
    FMap.MapsTo fn m mbox ->
    xstep (Read fn) tid
      (mk_state tmp mbox lock)
      (Some m)
      (mk_state tmp mbox lock)
      nil
  | StepReadNone : forall fn tmp mbox tid lock,
    ~ FMap.In fn mbox ->
    xstep (Read fn) tid
      (mk_state tmp mbox lock)
      None
      (mk_state tmp mbox lock)
      nil
  | StepDelete : forall fn tmp mbox tid lock,
    xstep (Delete fn) tid
      (mk_state tmp mbox lock)
      tt
      (mk_state tmp (FMap.remove fn mbox) lock)
      nil
  | StepLock : forall tmp mbox tid,
    xstep Lock tid
      (mk_state tmp mbox false)
      tt
      (mk_state tmp mbox true)
      nil
  | StepUnlock : forall tmp mbox tid lock,
    xstep Unlock tid
      (mk_state tmp mbox lock)
      tt
      (mk_state tmp mbox false)
      nil

  | StepExt : forall s tid `(extop : _ T) r,
    xstep (Ext extop) tid
      s
      r
      s
      (Event (extop, r) :: nil)
  .

  Definition step := xstep.

  Definition initP := initP.

End MailboxTmpAbsAPI.
Module MailboxTmpAbsHAPI := HLayer MailboxOp MailboxTmpAbsState MailboxTmpAbsAPI UserIdx.
