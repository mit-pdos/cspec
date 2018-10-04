Require Import CSPEC.
Require Import MailServerAPI.
Require Import MailFSPathAbsAPI.

Module MailFSPathOp <: Ops.

  Definition extopT := MailServerAPI.MailServerOp.extopT.

  Inductive xOp : Type -> Type :=
  | Create : forall (tmpfn : string * string), xOp bool
  | Write : forall (tmpfn : string * string) (data : string), xOp bool
  | Link : forall (tmpfn : string * string) (mboxfn : string * string), xOp bool
  | Unlink : forall (fn : string * string), xOp unit

  | GetTID : xOp nat
  | Random : xOp nat

  | List : forall (dir : string), xOp (list string)
  | Read : forall (fn : string * string), xOp (option string)

  | Lock : xOp unit
  | Unlock : xOp unit

  | Ext : forall `(op : extopT T), xOp T
  .

  Definition Op := xOp.

End MailFSPathOp.
Module MailFSPathHOp := HOps MailFSPathOp UserIdx.


Module MailFSPathAPI <: Layer MailFSPathOp MailFSPathAbsState.

  Import MailFSPathOp.
  Import MailFSPathAbsState.
  Import MailFSPathAbsAPI.

  Inductive xstep : forall T, Op T -> nat -> State -> T -> State -> list event -> Prop :=
  | StepCreateOK : forall fs tid tmpfn lock,
    xstep (Create tmpfn) tid
      (mk_state fs lock)
      true
      (mk_state (FMap.add tmpfn empty_string fs) lock)
      nil
  | StepCreateErr : forall fs tid tmpfn lock,
    xstep (Create tmpfn) tid
      (mk_state fs lock)
      false
      (mk_state fs lock)
      nil
  | StepWriteOK : forall fs tid tmpfn data lock,
    FMap.MapsTo tmpfn empty_string fs ->
    xstep (Write tmpfn data) tid
      (mk_state fs lock)
      true
      (mk_state (FMap.add tmpfn data fs) lock)
      nil
  | StepWriteErr1 : forall fs tid tmpfn data lock,
    xstep (Write tmpfn data) tid
      (mk_state fs lock)
      false
      (mk_state fs lock)
      nil
  | StepWriteErr2 : forall fs tid tmpfn data data' lock,
    FMap.MapsTo tmpfn empty_string fs ->
    xstep (Write tmpfn data) tid
      (mk_state fs lock)
      false
      (mk_state (FMap.add tmpfn data' fs) lock)
      nil
  | StepUnlink : forall fs tid fn lock,
    xstep (Unlink fn) tid
      (mk_state fs lock)
      tt
      (mk_state (FMap.remove fn fs) lock)
      nil
  | StepLinkOK : forall fs tid mailfn data tmpfn lock,
    FMap.MapsTo tmpfn data fs ->
    ~ FMap.In mailfn fs ->
    xstep (Link tmpfn mailfn) tid
      (mk_state fs lock)
      true
      (mk_state (FMap.add mailfn data fs) lock)
      nil
  | StepLinkErr : forall fs tid mailfn tmpfn lock,
    xstep (Link tmpfn mailfn) tid
      (mk_state fs lock)
      false
      (mk_state fs lock)
      nil

  | StepList : forall fs tid r dirname lock,
    FMap.is_permutation_key r (drop_dirname (filter_dir dirname fs)) ->
    xstep (List dirname) tid
      (mk_state fs lock)
      r
      (mk_state fs lock)
      nil

  | StepGetTID : forall s tid,
    xstep GetTID tid
      s
      tid
      s
      nil
  | StepRandom : forall s tid r,
    xstep Random tid
      s
      r
      s
      nil

  | StepReadOK : forall fn fs tid m lock,
    FMap.MapsTo fn m fs ->
    xstep (Read fn) tid
      (mk_state fs lock)
      (Some m)
      (mk_state fs lock)
      nil
  | StepReadNone : forall fn fs tid lock,
    ~ FMap.In fn fs ->
    xstep (Read fn) tid
      (mk_state fs lock)
      None
      (mk_state fs lock)
      nil

  | StepLock : forall fs tid,
    xstep Lock tid
      (mk_state fs false)
      tt
      (mk_state fs true)
      nil
  | StepUnlock : forall fs tid lock,
    xstep Unlock tid
      (mk_state fs lock)
      tt
      (mk_state fs false)
      nil

  | StepExt : forall s tid `(extop : extopT T) r,
    xstep (Ext extop) tid
      s
      r
      s
      (Event (extop, r) :: nil)
  .

  Definition step := xstep.

  Definition initP := initP.

End MailFSPathAPI.
Module MailFSPathHAPI := HLayer MailFSPathOp MailFSPathAbsState MailFSPathAPI UserIdx.
