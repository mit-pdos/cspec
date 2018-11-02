Require Import CSPEC.
Require Import MailServerAPI.
Require Import MailboxTmpAbsAPI.

Module DeliverOp.

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
Definition DeliverHOp := HOps DeliverOp.Op UserIdx.idx.

Module DeliverAPI.
  Import DeliverOp.
  Import MailboxTmpAbsState.

  Inductive xstep : forall T, Op T -> nat -> State -> T -> State -> list event -> Prop :=
  | StepCreateWriteTmpOK : forall tmp mbox tid data lock,
    xstep (CreateWriteTmp data) tid
      (mk_state tmp mbox lock)
      true
      (mk_state (FMap.add (tid, 0) data tmp) mbox lock)
      nil

  | StepCreateWriteTmpErr1 : forall tmp mbox tid data lock,
    xstep (CreateWriteTmp data) tid
      (mk_state tmp mbox lock)
      false
      (mk_state tmp mbox lock)
      nil
  | StepCreateWriteTmpErr2 : forall tmp mbox tid data data' lock,
    xstep (CreateWriteTmp data) tid
      (mk_state tmp mbox lock)
      false
      (mk_state (FMap.add (tid, 0) data' tmp) mbox lock)
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
    xstep (LinkMail) tid
      (mk_state tmp mbox lock)
      true
      (mk_state tmp (FMap.add (tid, mailfn) data mbox) lock)
      nil
  | StepLinkMailErr : forall tmp mbox tid lock,
    xstep (LinkMail) tid
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

  | StepRead : forall fn tmp mbox tid m lock,
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

  Definition initP := initP.

  Definition l : Layer.t DeliverOp.Op MailboxTmpAbsState.State :=
    {| Layer.step := step;
       Layer.initP := initP; |}.
                        
End DeliverAPI.
Definition DeliverHAPI := HLayer.t DeliverAPI.l UserIdx.idx.

Module DeliverProtocol.

  Import DeliverOp.
  Import MailboxTmpAbsState.

  Inductive xstep_allow : forall T, Op T -> nat -> State -> Prop :=
  | AllowCreateWriteTmp : forall tid tmp mbox data lock,
    xstep_allow (CreateWriteTmp data) tid (mk_state tmp mbox lock)
  | AllowLinkMail : forall tid tmp mbox lock,
    FMap.In (tid, 0) tmp ->
    xstep_allow (LinkMail) tid (mk_state tmp mbox lock)
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

  Definition p : Protocol.t DeliverOp.Op MailboxTmpAbsState.State :=
    {| Protocol.step_allow := step_allow; |}.

End DeliverProtocol.
Definition DeliverHProtocol := HProtocol.t UserIdx.idx DeliverProtocol.p.

Module DeliverRestrictedAPI.

  Definition step :=
    restricted_step DeliverAPI.l.(Layer.step) DeliverProtocol.p.(Protocol.step_allow).

  Definition initP := DeliverAPI.l.(Layer.initP).
  
  Definition l : Layer.t DeliverOp.Op MailboxTmpAbsState.State :=
    {| Layer.step := step;
       Layer.initP := initP; |}.

End DeliverRestrictedAPI.
Definition DeliverRestrictedHAPI := HLayer.t DeliverRestrictedAPI.l UserIdx.idx.
