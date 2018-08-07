Require Import CSPEC.
Require Import MailServerAPI.
Import RecordSetNotations.

Module MailServerLockAbsState <: State.

  Definition dir_contents := FMap.t (nat*nat) string.

  Record state_rec := mk_state {
    maildir : MailServerState.dir_contents;
    locked : option nat;
  }.

  Instance state_rec_settable : Settable _ :=
    mkSettable (pure mk_state <*> maildir <*> locked).

  Definition State := state_rec.
  Definition initP (s : State) := True.

End MailServerLockAbsState.
Module MailServerLockAbsHState := HState MailServerLockAbsState UserIdx.

Module MailServerLockAbsAPI <: Layer MailServerOp MailServerLockAbsState.

  Import MailServerOp.
  Import MailServerLockAbsState.

  Inductive xstep : forall T, Op T -> nat -> State -> T -> State -> list event -> Prop :=
  | StepDeliverOK : forall s m fn tid,
    ~ FMap.In fn (maildir s) ->
    xstep (Deliver m) tid
      s
      true
      s[maildir := FMap.add fn m (maildir s)]
      nil
  | StepDeliverErr : forall s m tid,
    xstep (Deliver m) tid
      s
      false
      s
      nil
  | StepPickup : forall s tid r,
    FMap.is_permutation_kv r (maildir s) ->
    xstep Pickup tid
      s
      r
      s
      nil
  | StepDelete : forall s tid id,
    xstep (Delete id) tid
      s
      tt
      s[maildir := FMap.remove id (maildir s)]
      nil

  | StepExt : forall s tid `(extop : extopT T) r,
    xstep (Ext extop) tid
      s
      r
      s
      (Event (extop, r) :: nil)
  .

  Definition step := xstep.

End MailServerLockAbsAPI.
Module MailServerLockAbsHAPI := HLayer MailServerOp MailServerLockAbsState MailServerLockAbsAPI UserIdx.
