Require Import POCS.
Require Import String.


Module MaildirAPI <: Layer.

  Definition dir_contents := FMap.t (nat*string) string.

  Inductive maildir_opT : Type -> Type :=
  | LinkMsg : forall (data : string), maildir_opT unit
  | List : maildir_opT (list (nat*string))
  | ReadMsg : forall (fn : nat*string), maildir_opT string
  .

  Definition opT := maildir_opT.
  Definition State := dir_contents.
  Definition initP (s : State) := True.

  Inductive xstep : forall T, opT T -> nat -> State -> T -> State -> list event -> Prop :=
  | StepLinkMsg : forall mbox tid fn m,
    ~ FMap.In (tid, fn) mbox ->
    xstep (LinkMsg m) tid
      mbox
      tt
      (FMap.add (tid, fn) m mbox)
      nil
  | StepReadMsg : forall mbox tid fn m,
    FMap.MapsTo fn m mbox ->
    xstep (ReadMsg fn) tid
      mbox
      m
      mbox
      nil
  | StepList : forall mbox tid,
    xstep List tid
      mbox
      (FMap.keys mbox)
      mbox
      nil
  .

  Definition step := xstep.

End MaildirAPI.


Module RL2API <: Layer.

  Import MaildirAPI.

  Inductive xopT : Type -> Type :=
  | LinkMsg : forall (fn : string) (data : string), xopT bool
  | List : xopT (list (nat * string))
  | ListRestricted : xopT (list string)
  | ReadMsg : forall (fn : nat*string), xopT string
  .

  Definition opT := xopT.
  Definition State := MaildirAPI.State.
  Definition initP (s : State) := True.

  Inductive xstep : forall T, opT T -> nat -> State -> T -> State -> list event -> Prop :=
  | StepLinkMsg0 : forall mbox tid fn m,
    ~ FMap.In (tid, fn) mbox ->
    xstep (LinkMsg fn m) tid
      mbox
      true
      (FMap.add (tid, fn) m mbox)
      nil
  | StepLinkMsg1 : forall mbox tid fn m,
    FMap.In (tid, fn) mbox ->
    xstep (LinkMsg fn m) tid
      mbox
      false
      mbox
      nil
  | StepReadMsg : forall mbox tid fn m,
    FMap.MapsTo fn m mbox ->
    xstep (ReadMsg fn) tid
      mbox
      m
      mbox
      nil
  | StepList : forall mbox tid,
    xstep List tid
      mbox
      (FMap.keys mbox)
      mbox
      nil
  | StepListRestricted : forall mbox tid r,
    (forall fn, In fn r <-> FMap.In (tid, fn) mbox) ->
    xstep ListRestricted tid
      mbox
      r
      mbox
      nil
  .

  Definition step := xstep.

End RL2API.


Module RestrictedListAPI <: Layer.

  Import RL2API.

  Definition opT := RL2API.opT.
  Definition State := RL2API.State.
  Definition initP (s : State) := True.

  Inductive step_allow : forall T, opT T -> nat -> State -> Prop :=
  | AllowLinkMsg : forall fn data mbox tid,
    ~ FMap.In (tid, fn) mbox ->
    step_allow (LinkMsg fn data) tid mbox
  | AllowList : forall mbox tid,
    step_allow List tid mbox
  | AllowListRestricted : forall mbox tid,
    step_allow ListRestricted tid mbox
  | AllowReadMsg : forall mbox tid fn,
    step_allow (ReadMsg fn) tid mbox
  .

  Definition step :=
    restricted_step RL2API.step step_allow.

End RestrictedListAPI.


Module RawDirAPI <: Layer.

  Import MaildirAPI.

  Inductive rawdir_opT : Type -> Type :=
  | LinkMsg : forall (fn : string) (data : string), rawdir_opT bool
  | List : rawdir_opT (list (nat * string))
  | ReadMsg : forall (fn : nat*string), rawdir_opT string
  | GetTID : rawdir_opT nat
  .

  Definition opT := rawdir_opT.
  Definition State := MaildirAPI.State.
  Definition initP (s : State) := True.

  Inductive xstep : forall T, opT T -> nat -> State -> T -> State -> list event -> Prop :=
  | StepLinkMsg0 : forall mbox tid fn m,
    ~ FMap.In (tid, fn) mbox ->
    xstep (LinkMsg fn m) tid
      mbox
      true
      (FMap.add (tid, fn) m mbox)
      nil
  | StepLinkMsg1 : forall mbox tid fn m,
    FMap.In (tid, fn) mbox ->
    xstep (LinkMsg fn m) tid
      mbox
      false
      mbox
      nil
  | StepReadMsg : forall mbox tid fn m,
    FMap.MapsTo fn m mbox ->
    xstep (ReadMsg fn) tid
      mbox
      m
      mbox
      nil
  | StepList : forall mbox tid,
    xstep List tid
      mbox
      (FMap.keys mbox)
      mbox
      nil
  | StepGetTID : forall mbox tid,
    xstep GetTID tid
      mbox
      tid
      mbox
      nil
  .

  Definition step := xstep.

End RawDirAPI.


Module LinkMsgRule <: ProcRule RL2API.

  Definition loopInv (s : RL2API.State) (tid : nat) := True.

  Definition follows_protocol (ts : @threads_state RL2API.opT) :=
    forall s,
      follows_protocol_s RL2API.step RestrictedListAPI.step_allow loopInv ts s.

End LinkMsgRule.
