Require Import CSPEC.
Require Import MailServerAPI.
Require Import MailServerLockAbsAPI.

Module MailboxOp.

  Definition extopT := MailServerAPI.MailServerOp.extopT.

  Inductive xOp : Type -> Type :=
  | Deliver : forall (m : string), xOp bool
  | List : xOp (list (nat*nat))
  | Read : forall (fn : nat*nat), xOp (option string)
  | Delete : forall (fn : nat*nat), xOp unit
  | Lock : xOp unit
  | Unlock : xOp unit
  | Ext : forall `(op : extopT T), xOp T
  .

  Definition Op := xOp.

End MailboxOp.
Definition MailboxHOp := HOps MailboxOp.Op UserIdx.idx.


Module MailboxAPI.

  Import MailboxOp.
  Import MailServerLockAbsState.

  Inductive xstep : forall T, Op T -> nat -> State -> T -> State -> list event -> Prop :=
  | StepDeliverOK : forall m mbox tid fn lock,
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

  | StepExt : forall s tid `(extop : extopT T) r,
    xstep (Ext extop) tid
      s
      r
      s
      (Event (extop, r) :: nil)
  .

  Definition step := xstep.

  Definition initP := initP.

  Definition l : Layer.t MailboxOp.Op MailServerLockAbsState.State :=
    {| Layer.step := step;
       Layer.initP := initP; |}.
                    
End MailboxAPI.
Definition MailboxHAPI := HLayer.t MailboxAPI.l UserIdx.idx.


Module MailboxProtocol.

  Import MailboxOp.
  Import MailServerLockAbsState.

  Inductive xstep_allow : forall T, Op T -> nat -> State -> Prop :=
  | AllowDeliver : forall m tid s,
    xstep_allow (Deliver m) tid s
  | AllowList : forall tid s,
    xstep_allow List tid s
  | AllowRead : forall fn tid s,
    locked s = Some tid ->
    xstep_allow (Read fn) tid s
  | AllowDelete : forall fn tid s,
    locked s = Some tid ->
    xstep_allow (Delete fn) tid s
  | AllowLock : forall tid s,
    xstep_allow Lock tid s
  | AllowUnlock : forall tid s,
    locked s = Some tid ->
    xstep_allow Unlock tid s
  | AllowExt : forall tid s `(extop : _ T),
    xstep_allow (Ext extop) tid s
  .

  Definition step_allow := xstep_allow.

  Definition p : Protocol.t MailboxOp.Op MailServerLockAbsState.State :=
    {| Protocol.step_allow := step_allow; |}.

End MailboxProtocol.

Definition MailboxHProtocol := HProtocol.t UserIdx.idx MailboxProtocol.p.

Module MailboxRestrictedAPI.

  Definition step :=
    restricted_step MailboxAPI.step MailboxProtocol.step_allow.

  Definition initP := MailboxAPI.initP.

  Definition l : Layer.t MailboxOp.Op MailServerLockAbsState.State :=
    {| Layer.step := step;
       Layer.initP := initP; |}.

End MailboxRestrictedAPI.
Definition MailboxRestrictedHAPI := HLayer.t MailboxRestrictedAPI.l UserIdx.idx.
