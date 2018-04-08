Require Import POCS.
Require Import MailServerAPI.
Require Import MailFSStringAbsAPI.
Require Import MailFSAPI.

Module MailFSStringOp <: Ops.

  Definition extopT := MailServerAPI.MailServerOp.extopT.

  Inductive xopT : Type -> Type :=
  | CreateWriteTmp : forall (tmpfn : string) (data : string), xopT bool
  | LinkMail : forall (tmpfn : string) (mboxfn : string), xopT bool
  | UnlinkTmp : forall (tmpfn : string), xopT unit

  | GetTID : xopT nat
  | Random : xopT nat

  | List : xopT (list string)
  | Read : forall (fn : string), xopT (option string)
  | Delete : forall (fn : string), xopT unit
  | Lock : xopT unit
  | Unlock : xopT unit

  | Ext : forall `(op : extopT T), xopT T
  .

  Definition opT := xopT.

End MailFSStringOp.
Module MailFSStringHOp := HOps MailFSStringOp UserIdx.


Module MailFSStringAPI <: Layer MailFSStringOp MailFSStringAbsState.

  Import MailFSStringOp.
  Import MailFSStringAbsState.

  Inductive xstep : forall T, opT T -> nat -> State -> T -> State -> list event -> Prop :=
  | StepCreateWriteTmpOK : forall tmp mbox tid tmpfn data lock,
    xstep (CreateWriteTmp tmpfn data) tid
      (mk_state tmp mbox lock)
      true
      (mk_state (FMap.add tmpfn data tmp) mbox lock)
      nil
  | StepCreateWriteTmpErr1 : forall tmp mbox tid tmpfn data lock,
    xstep (CreateWriteTmp tmpfn data) tid
      (mk_state tmp mbox lock)
      false
      (mk_state tmp mbox lock)
      nil
  | StepCreateWriteTmpErr2 : forall tmp mbox tid tmpfn data data' lock,
    xstep (CreateWriteTmp tmpfn data) tid
      (mk_state tmp mbox lock)
      false
      (mk_state (FMap.add tmpfn data' tmp) mbox lock)
      nil
  | StepUnlinkTmp : forall tmp mbox tid tmpfn lock,
    xstep (UnlinkTmp tmpfn) tid
      (mk_state tmp mbox lock)
      tt
      (mk_state (FMap.remove tmpfn tmp) mbox lock)
      nil
  | StepLinkMailOK : forall tmp mbox tid mailfn data tmpfn lock,
    FMap.MapsTo tmpfn data tmp ->
    ~ FMap.In mailfn mbox ->
    xstep (LinkMail tmpfn mailfn) tid
      (mk_state tmp mbox lock)
      true
      (mk_state tmp (FMap.add mailfn data mbox) lock)
      nil
  | StepLinkMailErr : forall tmp mbox tid mailfn tmpfn lock,
    xstep (LinkMail tmpfn mailfn) tid
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

End MailFSStringAPI.
Module MailFSStringHAPI := HLayer MailFSStringOp MailFSStringAbsState MailFSStringAPI UserIdx.
