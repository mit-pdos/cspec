Require Import POCS.
Require Import String.
Require Import MailServerAPI.
Require Import MailboxTmpAbsAPI.
Require Import DeliverAPI.


Module MailFSAPI <: Layer.

  Import MailServerAPI.
  Import MailboxTmpAbsAPI.

  Inductive xopT : Type -> Type :=
  | CreateWriteTmp : forall (data : string), xopT unit
  | LinkMail : forall (mboxfn : nat), xopT bool
  | UnlinkTmp : xopT unit

  | GetTID : xopT nat
  | Random : xopT nat

  | List : xopT (list (nat * nat))
  | Read : forall (fn : nat * nat), xopT (option string)
  | GetRequest : xopT request
  | Respond : forall (T : Type) (v : T), xopT unit
  .

  Definition opT := xopT.
  Definition State := DeliverAPI.State.
  Definition initP (s : State) := True.

  Inductive xstep : forall T, opT T -> nat -> State -> T -> State -> list event -> Prop :=
  | StepCreateWriteTmp : forall tmp mbox tid data,
    xstep (CreateWriteTmp data) tid
      (mk_state tmp mbox)
      tt
      (mk_state (FMap.add (tid, 0) data tmp) mbox)
      nil
  | StepUnlinkTmp : forall tmp mbox tid,
    xstep (UnlinkTmp) tid
      (mk_state tmp mbox)
      tt
      (mk_state (FMap.remove (tid, 0) tmp) mbox)
      nil
  | StepLinkMailOK : forall tmp mbox tid mailfn data,
    FMap.MapsTo (tid, 0) data tmp ->
    ~ FMap.In (tid, mailfn) mbox ->
    xstep (LinkMail mailfn) tid
      (mk_state tmp mbox)
      true
      (mk_state tmp (FMap.add (tid, mailfn) data mbox))
      nil
  | StepLinkMailErr : forall tmp mbox tid mailfn,
    ((~ FMap.In (tid, 0) tmp) \/
     (FMap.In (tid, mailfn) mbox)) ->
    xstep (LinkMail mailfn) tid
      (mk_state tmp mbox)
      false
      (mk_state tmp mbox)
      nil

  | StepList : forall tmp mbox tid r,
    FMap.is_permutation_key r mbox ->
    xstep List tid
      (mk_state tmp mbox)
      r
      (mk_state tmp mbox)
      nil

  | StepGetTID : forall tmp mbox tid,
    xstep GetTID tid
      (mk_state tmp mbox)
      tid
      (mk_state tmp mbox)
      nil
  | StepRandom : forall tmp mbox tid r,
    xstep Random tid
      (mk_state tmp mbox)
      r
      (mk_state tmp mbox)
      nil

  | StepReadOK : forall fn tmp mbox tid m,
    FMap.MapsTo fn m mbox ->
    xstep (Read fn) tid
      (mk_state tmp mbox)
      (Some m)
      (mk_state tmp mbox)
      nil
      
  | StepReadNone : forall fn tmp mbox tid m,
    ~FMap.MapsTo fn m mbox ->
    xstep (Read fn) tid
      (mk_state tmp mbox)
      None
      (mk_state tmp mbox)
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

End MailFSAPI.
