Require Import POCS.
Require Import String.
Require Import MailServerAPI.
Require Import MailServerLockAbsAPI.


Module MailboxAPI <: Layer.

  Import MailServerAPI.
  Import MailServerLockAbsAPI.

  Inductive xopT : Type -> Type :=
  | Deliver : forall (m : string), xopT unit
  | List : xopT (list (nat*nat))
  | Read : forall (fn : nat*nat), xopT (option string)
  | Delete : forall (fn : nat*nat), xopT unit
  | Lock : xopT unit
  | Unlock : xopT unit
  | GetRequest : xopT request
  | Respond : forall (T : Type) (v : T), xopT unit
  .

  Definition opT := xopT.
  Definition State := MailServerLockAbsAPI.State.
  Definition initP (s : State) := True.

  Inductive xstep : forall T, opT T -> nat -> State -> T -> State -> list event -> Prop :=
  | StepDeliver : forall m mbox tid fn lock,
    ~ FMap.In fn mbox ->
    xstep (Deliver m) tid
      (mk_state mbox lock)
      tt
      (mk_state (FMap.add fn m mbox) lock)
      nil
  | StepList : forall mbox tid r lock,
    FMap.is_permutation_key r mbox ->
    xstep List tid
      (mk_state mbox lock)
      r
      (mk_state mbox lock)
      nil

  | StepReadOK : forall fn mbox tid m lock,
    FMap.MapsTo fn m mbox ->
    xstep (Read fn) tid
      (mk_state mbox lock)
      (Some m)
      (mk_state mbox lock)
      nil
  | StepReadNone : forall fn mbox tid lock,
    ~ FMap.In fn mbox ->
    xstep (Read fn) tid
      (mk_state mbox lock)
      None
      (mk_state mbox lock)
      nil

  | StepDelete : forall fn mbox tid lock,
    xstep (Delete fn) tid
      (mk_state mbox lock)
      tt
      (mk_state (FMap.remove fn mbox) lock)
      nil

  | StepLock : forall mbox tid,
    xstep Lock tid
      (mk_state mbox None)
      tt
      (mk_state mbox (Some tid))
      nil
  | StepUnlock : forall mbox tid lock,
    xstep Unlock tid
      (mk_state mbox lock)
      tt
      (mk_state mbox None)
      nil

  | StepGetRequest : forall st tid r,
    xstep GetRequest tid
      st
      r
      st
      (Event r :: nil)
  | StepRespond : forall st tid T (v : T),
    xstep (Respond v) tid
      st
      tt
      st
      (Event v :: nil)
  .

  Definition step := xstep.

End MailboxAPI.


Module MailboxRestrictedAPI <: Layer.

  Import MailboxAPI.
  Import MailServerLockAbsAPI.

  Definition opT := MailboxAPI.opT.
  Definition State := MailboxAPI.State.
  Definition initP := MailboxAPI.initP.

  Inductive step_allow : forall T, opT T -> nat -> State -> Prop :=
  | AllowDeliver : forall m tid s,
    step_allow (Deliver m) tid s
  | AllowList : forall tid s,
    step_allow List tid s
  | AllowRead : forall fn tid s,
    locked s = Some tid ->
    step_allow (Read fn) tid s
  | AllowDelete : forall fn tid s,
    locked s = Some tid ->
    step_allow (Delete fn) tid s
  | AllowLock : forall tid s,
    step_allow Lock tid s
  | AllowUnlock : forall tid s,
    locked s = Some tid ->
    step_allow Unlock tid s
  | AllowGetRequest : forall tid s,
    step_allow GetRequest tid s
  | AllowRespond : forall `(r : T) tid s,
    step_allow (Respond r) tid s
  .

  Definition step :=
    restricted_step MailboxAPI.step step_allow.

End MailboxRestrictedAPI.


Module MailboxLockingRule <: ProcRule MailboxAPI.

  Definition follows_protocol (ts : @threads_state MailboxAPI.opT) :=
    forall s,
      follows_protocol_s MailboxAPI.step MailboxRestrictedAPI.step_allow ts s.

End MailboxLockingRule.
