Require Import POCS.
Require Import String.
Require Import MailServerAPI.
Require Import MailboxTmpAbsAPI.
Require Import DeliverAPI.


Module MailFSAPI <: Layer.

  Import MailServerAPI.
  Import MailboxTmpAbsAPI.

  Inductive xopT : Type -> Type :=
  | CreateTmp : xopT string
  | WriteTmp : forall (fn : string) (data : string), xopT unit
  | LinkMail : forall (tmpfn : string) (mboxfn : string), xopT unit
  | UnlinkTmp : forall (fn : string), xopT unit

  | GetTID : xopT nat
  | List : xopT (list (nat * string))
  | Read : forall (fn : nat * string), xopT string
  | GetRequest : xopT request
  | Respond : forall (T : Type) (v : T), xopT unit
  .

  Definition opT := xopT.
  Definition State := DeliverAPI.State.
  Definition initP (s : State) := True.

  Inductive xstep : forall T, opT T -> nat -> State -> T -> State -> list event -> Prop :=
  | StepCreateTmp : forall tmp mbox tid fn,
    ~ FMap.In (tid, fn) tmp ->
    xstep (CreateTmp) tid
      (mk_state tmp mbox)
      fn
      (mk_state (FMap.add (tid, fn) ""%string tmp) mbox)
      nil
  | StepWriteTmp : forall tmp mbox tid fn data,
    FMap.In (tid, fn) tmp ->
    xstep (WriteTmp fn data) tid
      (mk_state tmp mbox)
      tt
      (mk_state (FMap.add (tid, fn) data tmp) mbox)
      nil
  | StepUnlinkTmp : forall tmp mbox tid fn,
    xstep (UnlinkTmp fn) tid
      (mk_state tmp mbox)
      tt
      (mk_state (FMap.remove (tid, fn) tmp) mbox)
      nil
  | StepLinkMail : forall tmp mbox tid tmpfn mailfn data,
    FMap.MapsTo (tid, tmpfn) data tmp ->
    ~ FMap.In (tid, mailfn) mbox ->
    xstep (LinkMail tmpfn mailfn) tid
      (mk_state tmp mbox)
      tt
      (mk_state tmp (FMap.add (tid, mailfn) data mbox))
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

End MailFSAPI.
