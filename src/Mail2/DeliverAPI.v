Require Import POCS.
Require Import String.
Require Import MailServerAPI.
Require Import MailboxTmpAbsAPI.


Module DeliverAPI <: Layer.

  Import MailServerAPI.
  Import MailboxTmpAbsAPI.

  Inductive xopT : Type -> Type :=
  | CreateWriteTmp : forall (data : string), xopT unit
  | LinkMail : xopT bool
  | UnlinkTmp : xopT unit

  | List : xopT (list (nat * nat))
  | Read : forall (fn : nat * nat), xopT (option string)
  | GetRequest : xopT request
  | Respond : forall (T : Type) (v : T), xopT unit
  .

  Definition opT := xopT.
  Definition State := MailboxTmpAbsAPI.State.
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
  | StepLinkMailOK : forall tmp mbox tid mailfn data r,
    FMap.MapsTo (tid, 0) data tmp ->
    ~ FMap.In (tid, mailfn) mbox ->
    xstep (LinkMail) tid
      (mk_state tmp mbox)
      r
      (mk_state tmp (FMap.add (tid, mailfn) data mbox))
      nil
  | StepLinkMailErr : forall tmp mbox tid r,
    ~ FMap.In (tid, 0) tmp ->
    xstep (LinkMail) tid
      (mk_state tmp mbox)
      r
      (mk_state tmp mbox)
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
      (Some m)
      (mk_state tmp mbox)
      nil

  | StepReadNone : forall fn tmp mbox tid,
    ~ FMap.In fn mbox ->
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

End DeliverAPI.


Module DeliverRestrictedAPI <: Layer.

  Import DeliverAPI.
  Import MailboxTmpAbsAPI.

  Definition opT := DeliverAPI.opT.
  Definition State := DeliverAPI.State.
  Definition initP (s : State) := True.

  Inductive step_allow : forall T, opT T -> nat -> State -> Prop :=
  | AllowCreateWriteTmp : forall tid tmp mbox data,
    step_allow (CreateWriteTmp data) tid (mk_state tmp mbox)
  | AllowLinkMail : forall tid tmp mbox,
    FMap.In (tid, 0) tmp ->
    step_allow (LinkMail) tid (mk_state tmp mbox)
  | AllowUnlinkTmp : forall tid s,
    step_allow (UnlinkTmp) tid s
  | AllowList : forall tid s,
    step_allow List tid s
  | AllowRead : forall tid s fn,
    step_allow (Read fn) tid s
  | AllowGetRequest : forall tid s,
    step_allow GetRequest tid s
  | AllowRespond : forall tid s T (r : T),
    step_allow (Respond r) tid s
  .

  Definition step :=
    restricted_step DeliverAPI.step step_allow.

End DeliverRestrictedAPI.


Module DeliverTmpExistenceRule <: ProcRule DeliverAPI.

  Definition follows_protocol (ts : @threads_state DeliverAPI.opT) :=
    forall s,
      follows_protocol_s DeliverAPI.step DeliverRestrictedAPI.step_allow ts s.

End DeliverTmpExistenceRule.
