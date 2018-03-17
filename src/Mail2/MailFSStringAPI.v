Require Import POCS.
Require Import String.
Require Import MailServerAPI.
Require Import MailFSStringAbsAPI.
Require Import MailFSAPI.


Module MailFSStringAPI <: Layer.

  Import MailServerAPI.
  Import MailFSStringAbsAPI.

  Inductive xopT : Type -> Type :=
  | CreateWriteTmp : forall (tmpfn : string) (data : string), xopT unit
  | LinkMail : forall (tmpfn : string) (mboxfn : string), xopT bool
  | UnlinkTmp : forall (tmpfn : string), xopT unit

  | GetTID : xopT nat
  | Random : xopT nat

  | List : xopT (list string)
  | Read : forall (fn : string), xopT (option string)
  | Delete : forall (fn : string), xopT unit
  | Lock : xopT unit
  | Unlock : xopT unit
  | GetRequest : xopT request
  | Respond : forall (T : Type) (v : T), xopT unit
  .

  Definition opT := xopT.

  Definition State := MailFSStringAbsAPI.State.
  Definition initP (s : State) := True.

  Inductive xstep : forall T, opT T -> nat -> State -> T -> State -> list event -> Prop :=
  | StepCreateWriteTmp : forall tmp mbox tid tmpfn data lock,
    xstep (CreateWriteTmp tmpfn data) tid
      (mk_state tmp mbox lock)
      tt
      (mk_state (FMap.add tmpfn data tmp) mbox lock)
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
    ((~ FMap.In tmpfn tmp) \/
     (FMap.In mailfn mbox)) ->
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

  | StepGetRequest : forall s tid r,
    xstep GetRequest tid
      s
      r
      s
      (Event r :: nil)
  | StepRespond : forall s tid T (v : T),
    xstep (Respond v) tid
      s
      tt
      s
      (Event v :: nil)
  .

  Definition step := xstep.

End MailFSStringAPI.
