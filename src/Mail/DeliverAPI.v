Require Import CSPEC.
Require Import MailServerAPI.
Require Import MailboxTmpAbsAPI.
Import RecordSetNotations.


Module DeliverOp <: Ops.

  Definition extopT := MailServerAPI.MailServerOp.extopT.

  Inductive xOp : Type -> Type :=
  | CreateWriteTmp : forall (data : string), xOp bool
  | LinkMail : xOp bool
  | UnlinkTmp : xOp unit

  | List : xOp (list (nat * nat))
  | Read : forall (fn : nat * nat), xOp (option string)
  | Delete : forall (fn : nat*nat), xOp unit
  | Lock : xOp unit
  | Unlock : xOp unit

  | Ext : forall `(op : extopT T), xOp T
  .

  Definition Op := xOp.

End DeliverOp.
Module DeliverHOp := HOps DeliverOp UserIdx.


Module DeliverAPI <: Layer DeliverOp MailboxTmpAbsState.

  Import DeliverOp.
  Import MailboxTmpAbsState.

  Inductive xstep : forall T, Op T -> nat -> State -> T -> State -> list event -> Prop :=
  | StepCreateWriteTmpOK : forall s s' tid data,
    s' = s[tmpdir := FMap.add (tid, 0) data (tmpdir s)] ->
    xstep (CreateWriteTmp data) tid
      s
      true
      s'
      nil

  | StepCreateWriteTmpErr1 : forall s tid data,
    xstep (CreateWriteTmp data) tid
      s
      false
      s
      nil
  | StepCreateWriteTmpErr2 : forall s s' tid data data',
    s' = s[tmpdir := FMap.add (tid, 0) data' (tmpdir s)] ->
    xstep (CreateWriteTmp data) tid
      s
      false
      s'
      nil

  | StepUnlinkTmp :
    `(s' = s[tmpdir := FMap.remove (tid, 0) (tmpdir s)] ->
      xstep (UnlinkTmp) tid
        s
        tt
        s'
        nil)
  | StepLinkMailOK :
    `(FMap.MapsTo (tid, 0) data (tmpdir s) ->
      ~ FMap.In (tid, mailfn) (maildir s) ->
      s' = s[maildir := FMap.add (tid, mailfn) data (maildir s)] ->
      xstep (LinkMail) tid
        s
        true
        s'
        nil)
  | StepLinkMailErr :
    `(xstep (LinkMail) tid
        s
        false
        s
        nil)

  | StepList :
    `(FMap.is_permutation_key r (maildir s) ->
      xstep List tid
        s
        r
        s
        nil)

  | StepRead : forall fn s tid m,
    FMap.MapsTo fn m (maildir s) ->
    xstep (Read fn) tid
      s
      (Some m)
      s
      nil

  | StepReadNone :
    `(~ FMap.In fn (maildir s) ->
      xstep (Read fn) tid
        s
        None
        s
        nil)

  | StepDelete :
    `(xstep (Delete fn) tid
        s
        tt
        s[maildir := FMap.remove fn (maildir s)]
        nil)

  | StepLock :
    `(locked s = false ->
      xstep Lock tid
        s
        tt
        s[locked := true]
        nil)
  | StepUnlock :
    `(xstep Unlock tid
        s
        tt
        s[locked := false]
        nil)

  | StepExt :
    `(xstep (@Ext T extop) tid
        s
        r
        s
        (Event (extop, r) :: nil))
  .

  Definition step := xstep.

End DeliverAPI.
Module DeliverHAPI := HLayer DeliverOp MailboxTmpAbsState DeliverAPI UserIdx.


Module DeliverProtocol <: Protocol DeliverOp MailboxTmpAbsState.

  Import DeliverOp.
  Import MailboxTmpAbsState.

  Inductive xstep_allow : forall T, Op T -> nat -> State -> Prop :=
  | AllowCreateWriteTmp : forall tid data s,
    xstep_allow (CreateWriteTmp data) tid s
  | AllowLinkMail : forall tid s,
    FMap.In (tid, 0) (tmpdir s) ->
    xstep_allow (LinkMail) tid s
  | AllowUnlinkTmp : forall tid s,
    xstep_allow (UnlinkTmp) tid s
  | AllowList : forall tid s,
    xstep_allow List tid s
  | AllowRead : forall tid s fn,
    xstep_allow (Read fn) tid s
  | AllowDelete : forall tid s fn,
    xstep_allow (Delete fn) tid s
  | AllowLock : forall tid s,
    xstep_allow Lock tid s
  | AllowUnlock : forall tid s,
    xstep_allow Unlock tid s
  | AllowExt : forall tid s `(extop : _ T),
    xstep_allow (Ext extop) tid s
  .

  Definition step_allow := xstep_allow.

End DeliverProtocol.
Module DeliverHProtocol := HProtocol DeliverOp MailboxTmpAbsState DeliverProtocol UserIdx.


Module DeliverRestrictedAPI <: Layer DeliverOp MailboxTmpAbsState.

  Definition step :=
    restricted_step DeliverAPI.step DeliverProtocol.step_allow.

End DeliverRestrictedAPI.
Module DeliverRestrictedHAPI := HLayer DeliverOp MailboxTmpAbsState DeliverRestrictedAPI UserIdx.
