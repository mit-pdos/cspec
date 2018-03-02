Require Import POCS.
Require Import String.
Require Import MailServerAPI.
Require Import MailboxTmpAbsAPI.


Module DeliverAPI <: Layer.

  Import MailServerAPI.
  Import MailboxTmpAbsAPI.

  Inductive xopT : Type -> Type :=
  | CreateWriteTmp : forall (data : string), xopT unit
  | LinkMail : xopT unit
  | UnlinkTmp : xopT unit

  | List : xopT (list (nat * string))
  | Read : forall (fn : nat * string), xopT string
  | GetRequest : xopT request
  | Respond : forall (T : Type) (v : T), xopT unit
  .

  Definition opT := xopT.
  Definition State := MailboxTmpAbsAPI.State.
  Definition initP (s : State) := True.

  Inductive xstep : forall T, opT T -> nat -> State -> T -> State -> list event -> Prop :=
  | StepCreateWriteTmp : forall tmp mbox tid data,
    ~ FMap.In (tid, ""%string) tmp ->
    xstep (CreateWriteTmp data) tid
      (mk_state tmp mbox)
      tt
      (mk_state (FMap.add (tid, ""%string) data tmp) mbox)
      nil
  | StepUnlinkTmp : forall tmp mbox tid,
    xstep (UnlinkTmp) tid
      (mk_state tmp mbox)
      tt
      (mk_state (FMap.remove (tid, ""%string) tmp) mbox)
      nil
  | StepLinkMail : forall tmp mbox tid mailfn data,
    FMap.MapsTo (tid, ""%string) data tmp ->
    ~ FMap.In (tid, mailfn) mbox ->
    xstep (LinkMail) tid
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

End DeliverAPI.
