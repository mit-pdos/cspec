Require Import CSPEC.
Require Import MailServerAPI.

Module MailServerLockAbsState <: State.

  Definition dir_contents := FMap.t (nat*nat) string.
  
  Record state_rec := mk_state {
    maildir : MailServerState.dir_contents;
    locked : option nat;
  }.

  Definition State := state_rec.
  Definition initP (s : State) := True.

End MailServerLockAbsState.
Module MailServerLockAbsHState := HState MailServerLockAbsState UserIdx.

Module MailServerLockAbsAPI <: Layer MailServerOp MailServerLockAbsState.

  Import MailServerOp.
  Import MailServerLockAbsState.
  
  Inductive xstep : forall T, Op T -> nat -> State -> T -> State -> list event -> Prop :=
  | StepDeliverOK : forall m mbox fn tid lock,
    ~ FMap.In fn mbox ->
    xstep (Deliver m) tid
      (mk_state mbox lock)
      true
      (mk_state (FMap.add fn m mbox) lock)
      nil
  | StepDeliverErr : forall m mbox tid lock,
    xstep (Deliver m) tid
      (mk_state mbox lock)
      false
      (mk_state mbox lock)
      nil
  | StepPickup : forall mbox tid r lock,
    FMap.is_permutation_kv r mbox ->
    xstep Pickup tid
      (mk_state mbox lock)
      r
      (mk_state mbox lock)
      nil
  | StepDelete : forall mbox tid id lock,
    xstep (Delete id) tid
      (mk_state mbox lock)
      tt
      (mk_state (FMap.remove id mbox) lock)
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
