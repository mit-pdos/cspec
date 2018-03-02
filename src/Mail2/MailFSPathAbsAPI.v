Require Import POCS.
Require Import String.
Require Import MailServerAPI.
Require Import MailServerDirAPI.
Require Import MailboxTmpAbsAPI.
Require Import MailFSAPI.

Import ListNotations.
Open Scope string.

Module MailFSPathAbsAPI <: Layer.

  Import MailServerAPI.
  Import MailFSAPI.

  Definition opT := xopT.

  Definition fs_contents := FMap.t (string * (nat*string)) string.
  
  Definition State := fs_contents.
  Definition initP (s : State) := True.

  Parameter mk_state: MailServerDirAPI.dir_contents -> MailServerDirAPI.dir_contents -> fs_contents.
  
  Inductive xstep : forall T, opT T -> nat -> State -> T -> State -> list event -> Prop :=
  | StepCreateTmp : forall tmp mbox tid fn,
      let state := mk_state tmp mbox in
    ~ FMap.In (tid, fn) tmp ->
    xstep (CreateTmp) tid
      state
      fn
      ((FMap.add ("tmp", (tid, fn)) "") state)
      nil
  | StepWriteTmp : forall tmp mbox tid fn data,
    let state := mk_state tmp mbox in
    FMap.In (tid, fn) tmp ->
    xstep (WriteTmp fn data) tid
      state
      tt
      ((FMap.add ("tmp", (tid, fn)) data) state)
      nil
  | StepUnlinkTmp : forall tmp mbox tid fn,
    let state := mk_state tmp mbox in
    xstep (UnlinkTmp fn) tid
      state
      tt
      (FMap.remove ("tmp", (tid, fn)) state)
      nil
  | StepLinkMail : forall tmp mbox tid tmpfn mailfn data,
    let state := mk_state tmp mbox in
    FMap.MapsTo (tid, tmpfn) data tmp ->
    ~ FMap.In (tid, mailfn) mbox ->
    xstep (LinkMail tmpfn mailfn) tid
      state
      tt
      ((FMap.add ("maildir", (tid, mailfn)) data) state)
      nil
  | StepList : forall tmp mbox tid r,
    let state := mk_state tmp mbox in
    FMap.is_permutation_key r mbox ->
    xstep List tid
      state
      r
      state
      nil

  | StepGetTID : forall tmp mbox tid,
    let state := mk_state tmp mbox in
    xstep GetTID tid
      state
      tid
      state
      nil

  | StepRead : forall fn tmp mbox tid m,
    let state := mk_state tmp mbox in
    FMap.MapsTo fn m mbox ->
    xstep (Read fn) tid
      state
      m
      state
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

End MailFSPathAbsAPI.