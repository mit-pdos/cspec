Require Import POCS.
Require Import String.
Require Import MailServerAPI.
Require Import MailboxTmpAbsAPI.
Require Import DeliverAPI.


Module DeliverListTidAPI <: Layer.

  Import MailServerAPI.
  Import DeliverAPI.
  Import MailboxTmpAbsAPI.

  Inductive xopT : Type -> Type :=
  | CreateTmp : xopT string
  | WriteTmp : forall (fn : string) (data : string), xopT unit
  | LinkMail : forall (tmpfn : string) (mboxfn : string), xopT unit
  | UnlinkTmp : forall (fn : string), xopT unit

  | List : xopT (list (nat * string))
  | ListTid : xopT (list string)
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
  | StepListTid : forall tmp mbox tid r,
    (forall fn, In fn r <-> FMap.In (tid, fn) mbox) ->
    xstep ListTid tid
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

End DeliverListTidAPI.


Module DeliverListTidRestrictedAPI <: Layer.

  Import DeliverListTidAPI.
  Import MailboxTmpAbsAPI.

  Definition opT := DeliverListTidAPI.opT.
  Definition State := DeliverListTidAPI.State.
  Definition initP (s : State) := True.

  Inductive step_allow : forall T, opT T -> nat -> State -> Prop :=
  | AllowCreateTmp : forall tid s,
    step_allow CreateTmp tid s
  | AllowWriteTmp : forall tid s fn data,
    step_allow (WriteTmp fn data) tid s
  | AllowLinkMail : forall tid tmp mbox tmpfn mailfn,
    ~ FMap.In (tid, mailfn) mbox ->
    step_allow (LinkMail tmpfn mailfn) tid (mk_state tmp mbox)
  | AllowUnlinkTmp : forall tid s fn,
    step_allow (UnlinkTmp fn) tid s
  | AllowList : forall tid s,
    step_allow List tid s
  | AllowListTid : forall tid s,
    step_allow ListTid tid s
  | AllowRead : forall tid s fn,
    step_allow (Read fn) tid s
  | AllowGetRequest : forall tid s,
    step_allow GetRequest tid s
  | AllowRespond : forall tid s T (r : T),
    step_allow (Respond r) tid s
  .

  Definition step :=
    restricted_step DeliverListTidAPI.step step_allow.

End DeliverListTidRestrictedAPI.


Module LinkMailRule <: ProcRule DeliverListTidAPI.

  Definition loopInv (s : DeliverListTidAPI.State) (tid : nat) := True.

  Definition follows_protocol (ts : @threads_state DeliverListTidAPI.opT) :=
    forall s,
      follows_protocol_s DeliverListTidAPI.step DeliverListTidRestrictedAPI.step_allow loopInv ts s.

End LinkMailRule.
