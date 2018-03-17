Require Import POCS.
Require Import String.
Require Import MailServerAPI.
Require Import MailboxTmpAbsAPI.
Require Import DeliverAPI.


Module DeliverListTidAPI <: Layer.

  Import MailServerAPI.
  Import DeliverAPI.
  Import MailboxTmpAbsAPI.

  Inductive xopT : Type -> Type :=
  | CreateWriteTmp : forall (data : string), xopT unit
  | LinkMail : forall (mboxfn : nat), xopT bool
  | UnlinkTmp : xopT unit

  | List : xopT (list (nat * nat))
  | ListTid : xopT (list nat)
  | Read : forall (fn : nat * nat), xopT (option string)
  | Delete : forall (fn : nat * nat), xopT unit
  | Lock : xopT unit
  | Unlock : xopT unit

  | Ext : forall `(op : extopT T), xopT T
  .

  Definition opT := xopT.
  Definition State := DeliverAPI.State.
  Definition initP (s : State) := True.

  Inductive xstep : forall T, opT T -> nat -> State -> T -> State -> list event -> Prop :=
  | StepCreateWriteTmp : forall tmp mbox tid data lock,
    xstep (CreateWriteTmp data) tid
      (mk_state tmp mbox lock)
      tt
      (mk_state (FMap.add (tid, 0) data tmp) mbox lock)
      nil
  | StepUnlinkTmp : forall tmp mbox tid lock,
    xstep (UnlinkTmp) tid
      (mk_state tmp mbox lock)
      tt
      (mk_state (FMap.remove (tid, 0) tmp) mbox lock)
      nil
  | StepLinkMailOK : forall tmp mbox tid mailfn data lock,
    FMap.MapsTo (tid, 0) data tmp ->
    ~ FMap.In (tid, mailfn) mbox ->
    xstep (LinkMail mailfn) tid
      (mk_state tmp mbox lock)
      true
      (mk_state tmp (FMap.add (tid, mailfn) data mbox) lock)
      nil
  | StepLinkMailErr : forall tmp mbox tid mailfn lock,
    ((~ FMap.In (tid, 0) tmp) \/
     (FMap.In (tid, mailfn) mbox)) ->
    xstep (LinkMail mailfn) tid
      (mk_state tmp mbox lock)
      false
      (mk_state tmp mbox lock)
      nil

  | StepList : forall tmp mbox tid r lock,
    FMap.is_permutation_key r mbox ->
    xstep List tid
      (mk_state tmp mbox lock)
      r
      (mk_state tmp mbox lock)
      nil
  | StepListTid : forall tmp mbox tid r lock,
    (forall fn, FMap.In (tid, fn) mbox -> In fn r) ->
    xstep ListTid tid
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

  | StepExt : forall s tid `(extop : extopT T) r,
    xstep (Ext extop) tid
      s
      r
      s
      (Event (extop, r) :: nil)
  .

  Definition step := xstep.

End DeliverListTidAPI.


Module DeliverListTidRestrictedAPI <: Layer.

  Import DeliverListTidAPI.
  Import MailboxTmpAbsAPI.

  Definition opT := DeliverListTidAPI.opT.
  Definition State := DeliverListTidAPI.State.
  Definition initP (s : State) := True.

  Inductive step_allow : forall T, opT T -> nat -> State -> Prop :=
  | AllowCreateWriteTmp : forall tid s data,
    step_allow (CreateWriteTmp data) tid s
  | AllowLinkMail : forall tid tmp mbox mailfn lock,
    ~ FMap.In (tid, mailfn) mbox ->
    step_allow (LinkMail mailfn) tid (mk_state tmp mbox lock)
  | AllowUnlinkTmp : forall tid s,
    step_allow (UnlinkTmp) tid s
  | AllowList : forall tid s,
    step_allow List tid s
  | AllowListTid : forall tid s,
    step_allow ListTid tid s
  | AllowRead : forall tid s fn,
    step_allow (Read fn) tid s
  | AllowDelete : forall tid s fn,
    step_allow (Delete fn) tid s
  | AllowLock : forall tid s,
    step_allow Lock tid s
  | AllowUnlock : forall tid s,
    step_allow Unlock tid s
  | AllowExt : forall tid s `(extop : _ T),
    step_allow (Ext extop) tid s
  .

  Definition step :=
    restricted_step DeliverListTidAPI.step step_allow.

End DeliverListTidRestrictedAPI.


Module LinkMailRule <: ProcRule DeliverListTidAPI.

  Definition follows_protocol (ts : @threads_state DeliverListTidAPI.opT) :=
    forall s,
      follows_protocol_s DeliverListTidAPI.step DeliverListTidRestrictedAPI.step_allow ts s.

End LinkMailRule.
