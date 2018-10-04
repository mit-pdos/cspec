Require Import CSPEC.
Require Import MailServerAPI.
Require Import MailFSPathAPI.


Module MailFSMergedOp <: Ops.

  Definition extopT := MailServerAPI.MailServerOp.extopT.

  Inductive xOp : Type -> Type :=
  | Create : forall (fn : string * string * string), xOp bool
  | Write : forall (fn : string * string * string) (data : string), xOp bool
  | Link : forall (fn : string * string * string) (fn : string * string * string), xOp bool
  | Unlink : forall (fn : string * string * string), xOp unit

  | GetTID : xOp nat
  | Random : xOp nat

  | List : forall (dir : string * string), xOp (list string)
  | Read : forall (fn : string * string * string), xOp (option string)

  | Lock : forall (u : string), xOp unit
  | Unlock : forall (u : string), xOp unit
  | Exists : forall (u : string), xOp (CheckResult UserIdx.indexValid)

  | Ext : forall `(op : extopT T), xOp T
  .

  Definition Op := xOp.

End MailFSMergedOp.


Module MailFSMergedState <: State.

  Definition fs_contents := FMap.t (string * string * string) string.
  Definition locked_map := FMap.t string bool.

  Record state_rec := mk_state {
    fs : fs_contents;
    locked : locked_map;
  }.

  Definition State := state_rec.
  Definition initP (s : State) :=
    (forall u,
      UserIdx.indexValid u ->
      FMap.MapsTo u false (locked s)) /\
    fs s = FMap.empty.

End MailFSMergedState.


Definition filter_dir (dirname : string * string) (fs : MailFSMergedState.fs_contents) :=
  FMap.filter (fun '(dn, fn) => if dn == dirname then true else false) fs.

Definition drop_dirname (fs : MailFSMergedState.fs_contents) :=
  FMap.map_keys (fun '(dn, fn) => fn) fs.


Module MailFSMergedAPI <: Layer MailFSMergedOp MailFSMergedState.

  Import MailFSMergedOp.
  Import MailFSMergedState.

  (* TCB: these are the atomic semantics of the low-level operation the mail
  server is implemented on top of. There is no Coq implementation of these
  operations; it is trusted that the Haskell implementation in
  mail-test/lib/Interpreter.hs, when run on a file system, obeys these
  semantics. *)
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

  | StepLock : forall fs tid u locked,
    FMap.MapsTo u false locked ->
    xstep (Lock u) tid
      (mk_state fs locked)
      tt
      (mk_state fs (FMap.add u true locked))
      nil
  | StepLockErr : forall fs tid u locked,
    ~ FMap.In u locked ->
    xstep (Lock u) tid
      (mk_state fs locked)
      tt
      (mk_state fs locked)
      nil
  | StepUnlock : forall fs tid u locked,
    xstep (Unlock u) tid
      (mk_state fs locked)
      tt
      (mk_state fs (FMap.add u false locked))
      nil

  | StepExistsOK : forall fs tid u P locked,
    FMap.In u locked ->
    xstep (Exists u) tid
      (mk_state fs locked)
      (Present (exist _ u P))
      (mk_state fs locked)
      nil
  | StepExistsErr : forall fs tid u locked,
    ~ FMap.In u locked ->
    xstep (Exists u) tid
      (mk_state fs locked)
      Missing
      (mk_state fs locked)
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

End MailFSMergedAPI.


Module MailFSMergedAbsAPI <: Layer MailFSPathHOp MailFSMergedState.

  Import MailFSPathOp.
  Import MailFSPathHOp.
  Import MailFSMergedState.

  Inductive xstep : forall T, Op T -> nat -> State -> T -> State -> list event -> Prop :=
  | StepCreateOK : forall fs tid dir fn lock u P,
    xstep (Slice (exist _ u P) (Create (dir, fn))) tid
      (mk_state fs lock)
      true
      (mk_state (FMap.add (u, dir, fn) empty_string fs) lock)
      nil
  | StepCreateErr : forall fs tid dir fn lock u P,
    xstep (Slice (exist _ u P) (Create (dir, fn))) tid
      (mk_state fs lock)
      false
      (mk_state fs lock)
      nil
  | StepWriteOK : forall fs tid dir fn data lock u P,
    FMap.MapsTo (u, dir, fn) empty_string fs ->
    xstep (Slice (exist _ u P) (Write (dir, fn) data)) tid
      (mk_state fs lock)
      true
      (mk_state (FMap.add (u, dir, fn) data fs) lock)
      nil
  | StepWriteErr1 : forall fs tid dir fn data lock u P,
    xstep (Slice (exist _ u P) (Write (dir, fn) data)) tid
      (mk_state fs lock)
      false
      (mk_state fs lock)
      nil
  | StepWriteErr2 : forall fs tid dir fn data data' lock u P,
    FMap.MapsTo (u, dir, fn) empty_string fs ->
    xstep (Slice (exist _ u P) (Write (dir, fn) data)) tid
      (mk_state fs lock)
      false
      (mk_state (FMap.add (u, dir, fn) data' fs) lock)
      nil
  | StepUnlink : forall fs tid dir fn lock u P,
    xstep (Slice (exist _ u P) (Unlink (dir, fn))) tid
      (mk_state fs lock)
      tt
      (mk_state (FMap.remove (u, dir, fn) fs) lock)
      nil
  | StepLinkOK : forall fs tid srcdir srcfn data dstdir dstfn lock u P,
    FMap.MapsTo (u, srcdir, srcfn) data fs ->
    ~ FMap.In (u, dstdir, dstfn) fs ->
    xstep (Slice (exist _ u P) (Link (srcdir, srcfn) (dstdir, dstfn))) tid
      (mk_state fs lock)
      true
      (mk_state (FMap.add (u, dstdir, dstfn) data fs) lock)
      nil
  | StepLinkErr : forall fs tid srcdir srcfn dstdir dstfn lock u P,
    xstep (Slice (exist _ u P) (Link (srcdir, srcfn) (dstdir, dstfn))) tid
      (mk_state fs lock)
      false
      (mk_state fs lock)
      nil

  | StepList : forall fs tid r dirname lock u P,
    FMap.is_permutation_key r (drop_dirname (filter_dir (u, dirname) fs)) ->
    xstep (Slice (exist _ u P) (List dirname)) tid
      (mk_state fs lock)
      r
      (mk_state fs lock)
      nil

  | StepGetTID : forall s tid u P,
    xstep (Slice (exist _ u P) GetTID) tid
      s
      tid
      s
      nil
  | StepRandom : forall s tid r u P,
    xstep (Slice (exist _ u P) Random) tid
      s
      r
      s
      nil

  | StepReadOK : forall dir fn fs tid m lock u P,
    FMap.MapsTo (u, dir, fn) m fs ->
    xstep (Slice (exist _ u P) (Read (dir, fn))) tid
      (mk_state fs lock)
      (Some m)
      (mk_state fs lock)
      nil
  | StepReadNone : forall dir fn fs tid lock u P,
    ~ FMap.In (u, dir, fn) fs ->
    xstep (Slice (exist _ u P) (Read (dir, fn))) tid
      (mk_state fs lock)
      None
      (mk_state fs lock)
      nil

  | StepLock : forall fs tid u locked P,
    FMap.MapsTo u false locked ->
    xstep (Slice (exist _ u P) Lock) tid
      (mk_state fs locked)
      tt
      (mk_state fs (FMap.add u true locked))
      nil
  | StepLockErr : forall fs tid u locked P,
    ~ FMap.In u locked ->
    xstep (Slice (exist _ u P) Lock) tid
      (mk_state fs locked)
      tt
      (mk_state fs locked)
      nil
  | StepUnlock : forall fs tid u locked P,
    xstep (Slice (exist _ u P) Unlock) tid
      (mk_state fs locked)
      tt
      (mk_state fs (FMap.add u false locked))
      nil

  | StepExistsOK : forall fs tid u P locked,
    FMap.In u locked ->
    xstep (CheckSlice u) tid
      (mk_state fs locked)
      (Present (exist _ u P))
      (mk_state fs locked)
      nil
  | StepExistsErr : forall fs tid u locked,
    ~ FMap.In u locked ->
    xstep (CheckSlice u) tid
      (mk_state fs locked)
      Missing
      (mk_state fs locked)
      nil

  | StepExt : forall s tid `(extop : extopT T) r u P,
    xstep (Slice (exist _ u P) (Ext extop)) tid
      s
      r
      s
      (Event (extop, r) :: nil)
  .

  Definition step := xstep.

  Definition initP := initP.

End MailFSMergedAbsAPI.
