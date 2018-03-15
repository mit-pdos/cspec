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
  | LinkMail : forall (tmpfn : string) (mboxfn : string), xopT unit
  | UnlinkTmp : forall (tmpfn : string), xopT unit

  | GetTID : xopT nat
  | Random : xopT nat

  | List : xopT (list string)
  | Read : forall (fn : string), xopT string
  | GetRequest : xopT request
  | Respond : forall (T : Type) (v : T), xopT unit
  .

  Definition opT := xopT.

  Definition State := MailFSStringAbsAPI.State.
  Definition initP (s : State) := True.

  Inductive xstep : forall T, opT T -> nat -> State -> T -> State -> list event -> Prop :=
  | StepCreateWriteTmp : forall tmp mbox tid tmpfn data,
    xstep (CreateWriteTmp tmpfn data) tid
      (mk_state tmp mbox)
      tt
      (mk_state (FMap.add tmpfn data tmp) mbox)
      nil
  | StepUnlinkTmp : forall tmp mbox tid tmpfn,
    xstep (UnlinkTmp tmpfn) tid
      (mk_state tmp mbox)
      tt
      (mk_state (FMap.remove tmpfn tmp) mbox)
      nil
  | StepLinkMail : forall tmp mbox tid mailfn data tmpfn,
    FMap.MapsTo tmpfn data tmp ->
    xstep (LinkMail tmpfn mailfn) tid
      (mk_state tmp mbox)
      tt
      (mk_state tmp (FMap.add mailfn data mbox))
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

  | StepRead : forall fn tmp mbox tid m,
    FMap.MapsTo fn m mbox ->
    xstep (Read fn) tid
      (mk_state tmp mbox)
      m
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

End MailFSStringAPI.
