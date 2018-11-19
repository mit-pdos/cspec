Require Import CSPEC.
Require Import MailServerAPI.
Require Import MailboxTmpAbsAPI.
Require Import DeliverAPI.

Module MailFSOp.

  Definition extopT := MailServerAPI.MailServerOp.extopT.

  Inductive xOp : Type -> Type :=
  | CreateTmp : xOp bool
  | WriteTmp : forall (data : string), xOp bool
  | LinkMail : forall (mboxfn : nat), xOp bool
  | UnlinkTmp : xOp unit

  | GetTID : xOp nat
  | Random : xOp nat

  | List : xOp (list (nat * nat))
  | Read : forall (fn : nat * nat), xOp (option string)
  | Delete : forall (fn : nat * nat), xOp unit
  | Lock : xOp unit
  | Unlock : xOp unit

  | Ext : forall `(op : extopT T), xOp T
  .

  Definition Op := xOp.

End MailFSOp.
Definition MailFSHOp := HOps MailFSOp.Op UserIdx.idx.

Module MailFSAPI.

  Import MailFSOp.
  Import MailboxTmpAbsState.

  Inductive xstep : forall T, Op T -> nat -> State -> T -> State -> list event -> Prop :=
  | StepCreateTmpOk : forall tmp mbox tid lock,
    xstep (CreateTmp) tid
      (mk_state tmp mbox lock)
      true
      (mk_state (FMap.add (tid, 0) empty_string tmp) mbox lock)
      nil
  | StepCreateTmpErr : forall tmp mbox tid lock,
    xstep (CreateTmp) tid
      (mk_state tmp mbox lock)
      false
      (mk_state tmp mbox lock)
      nil
  | StepWriteTmpOk : forall tmp mbox tid data lock,
    FMap.MapsTo (tid, 0) empty_string tmp ->
    xstep (WriteTmp data) tid
      (mk_state tmp mbox lock)
      true
      (mk_state (FMap.add (tid, 0) data tmp) mbox lock)
      nil
  | StepWriteTmpErr1 : forall tmp mbox tid data lock,
    xstep (WriteTmp data) tid
      (mk_state tmp mbox lock)
      false
      (mk_state tmp mbox lock)
      nil
  | StepWriteTmpErr2 : forall tmp mbox tid data data' lock,
    FMap.MapsTo (tid, 0) empty_string tmp ->
    xstep (WriteTmp data) tid
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
    xstep (LinkMail mailfn) tid
      (mk_state tmp mbox lock)
      true
      (mk_state tmp (FMap.add (tid, mailfn) data mbox) lock)
      nil
  | StepLinkMailErr : forall tmp mbox tid mailfn lock,
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

  | StepGetTID : forall tmp mbox tid lock,
    xstep GetTID tid
      (mk_state tmp mbox lock)
      tid
      (mk_state tmp mbox lock)
      nil
  | StepRandom : forall tmp mbox tid r lock,
    xstep Random tid
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

  Definition initP := initP.

  Definition l : Layer.t MailFSOp.Op MailboxTmpAbsState.State.
    refine {| Layer.step := step;
              Layer.initP := initP; |}.
  Defined.

End MailFSAPI.
Definition MailFSHAPI := HLayer.t MailFSAPI.l UserIdx.idx.
