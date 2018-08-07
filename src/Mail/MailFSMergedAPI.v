Require Import CSPEC.
Require Import MailServerAPI.
Require Import MailFSPathAPI.


Module MailFSMergedOp <: Ops.

  Definition extopT := MailServerAPI.MailServerOp.extopT.

  Inductive xOp : Type -> Type :=
  | CreateWrite : forall (fn : string * string * string) (data : string), xOp bool
  | Link : forall (fn : string * string * string) (fn : string * string * string), xOp bool
  | Unlink : forall (fn : string * string * string), xOp unit

  | GetTID : xOp nat
  | Random : xOp nat

  | DirOpen : forall (dir : string * string), xOp readdir_handle
  | DirNext : forall (h : readdir_handle), xOp (option string)
  | DirClose : forall (h : readdir_handle), xOp unit

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
  Definition handle_map := FMap.t readdir_handle ((string*string) * FSet.t string).

  Record state_rec := mk_state {
    fs : fs_contents;
    locked : locked_map;
    handles : handle_map;
  }.

  Definition State := state_rec.
  Definition initP (s : State) :=
    forall u,
      UserIdx.indexValid u ->
      FMap.In u (locked s).

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
  | StepCreateWriteOK : forall fs tid tmpfn data lock dirs,
    xstep (CreateWrite tmpfn data) tid
      (mk_state fs lock dirs)
      true
      (mk_state (FMap.add tmpfn data fs) lock dirs)
      nil
  | StepCreateWriteErr1 : forall fs tid tmpfn data lock dirs,
    xstep (CreateWrite tmpfn data) tid
      (mk_state fs lock dirs)
      false
      (mk_state fs lock dirs)
      nil
  | StepCreateWriteErr2 : forall fs tid tmpfn data data' lock dirs,
    xstep (CreateWrite tmpfn data) tid
      (mk_state fs lock dirs)
      false
      (mk_state (FMap.add tmpfn data' fs) lock dirs)
      nil
  | StepUnlink : forall fs tid fn lock dirs,
    xstep (Unlink fn) tid
      (mk_state fs lock dirs)
      tt
      (mk_state (FMap.remove fn fs) lock dirs)
      nil
  | StepLinkOK : forall fs tid mailfn data tmpfn lock dirs,
    FMap.MapsTo tmpfn data fs ->
    ~ FMap.In mailfn fs ->
    xstep (Link tmpfn mailfn) tid
      (mk_state fs lock dirs)
      true
      (mk_state (FMap.add mailfn data fs) lock dirs)
      nil
  | StepLinkErr : forall fs tid mailfn tmpfn lock dirs,
    xstep (Link tmpfn mailfn) tid
      (mk_state fs lock dirs)
      false
      (mk_state fs lock dirs)
      nil

  | StepList : forall fs tid r dirname lock dirs,
    FMap.is_permutation_key r (drop_dirname (filter_dir dirname fs)) ->
    xstep (List dirname) tid
      (mk_state fs lock dirs)
      r
      (mk_state fs lock dirs)
      nil

  | StepDirOpen : forall fs lock dirs tid r dirname,
    ~ FMap.In r dirs ->
    xstep (DirOpen dirname) tid
      (mk_state fs lock dirs)
      r
      (mk_state fs lock (FMap.add r (dirname, FSet.empty) dirs))
      nil
  | StepDirNext : forall fs lock dirs dirname dirnames tid h name,
    FMap.MapsTo h (dirname, dirnames) dirs ->
    FMap.In (dirname, name) fs ->
    ~ FMap.In name dirnames ->
    xstep (DirNext h) tid
      (mk_state fs lock dirs)
      (Some name)
      (mk_state fs lock (FMap.add h (dirname, FSet.add name dirnames) dirs))
      nil
  | StepDirNextEOF : forall fs lock dirs dirname dirnames tid h,
    FMap.MapsTo h (dirname, dirnames) dirs ->
    (forall name, FMap.In (dirname, name) fs -> FMap.In name dirnames) ->
    xstep (DirNext h) tid
      (mk_state fs lock dirs)
      None
      (mk_state fs lock dirs)
      nil
  | StepDirClose : forall fs lock dirs tid h,
    xstep (DirClose h) tid
      (mk_state fs lock dirs)
      tt
      (mk_state fs lock (FMap.remove h dirs))
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

  | StepReadOK : forall fn fs tid m lock dirs,
    FMap.MapsTo fn m fs ->
    xstep (Read fn) tid
      (mk_state fs lock dirs)
      (Some m)
      (mk_state fs lock dirs)
      nil
  | StepReadNone : forall fn fs tid lock dirs,
    ~ FMap.In fn fs ->
    xstep (Read fn) tid
      (mk_state fs lock dirs)
      None
      (mk_state fs lock dirs)
      nil

  | StepLock : forall fs tid u locked dirs,
    FMap.MapsTo u false locked ->
    xstep (Lock u) tid
      (mk_state fs locked dirs)
      tt
      (mk_state fs (FMap.add u true locked) dirs)
      nil
  | StepLockErr : forall fs tid u locked dirs,
    ~ FMap.In u locked ->
    xstep (Lock u) tid
      (mk_state fs locked dirs)
      tt
      (mk_state fs locked dirs)
      nil
  | StepUnlock : forall fs tid u locked dirs,
    xstep (Unlock u) tid
      (mk_state fs locked dirs)
      tt
      (mk_state fs (FMap.add u false locked) dirs)
      nil

  | StepExistsOK : forall fs tid u P locked dirs,
    FMap.In u locked ->
    xstep (Exists u) tid
      (mk_state fs locked dirs)
      (Present (exist _ u P))
      (mk_state fs locked dirs)
      nil
  | StepExistsErr : forall fs tid u locked dirs,
    ~ FMap.In u locked ->
    xstep (Exists u) tid
      (mk_state fs locked dirs)
      Missing
      (mk_state fs locked dirs)
      nil

  | StepExt : forall s tid `(extop : extopT T) r,
    xstep (Ext extop) tid
      s
      r
      s
      (Event (extop, r) :: nil)
  .

  Definition step := xstep.

End MailFSMergedAPI.


Module MailFSMergedAbsAPI <: Layer MailFSPathHOp MailFSMergedState.

  Import MailFSPathOp.
  Import MailFSPathHOp.
  Import MailFSMergedState.

  Inductive xstep : forall T, Op T -> nat -> State -> T -> State -> list event -> Prop :=
  | StepCreateWriteOK : forall fs tid dir fn data lock u P dirs,
    xstep (Slice (exist _ u P) (CreateWrite (dir, fn) data)) tid
      (mk_state fs lock dirs)
      true
      (mk_state (FMap.add (u, dir, fn) data fs) lock dirs)
      nil
  | StepCreateWriteErr1 : forall fs tid dir fn data lock u P dirs,
    xstep (Slice (exist _ u P) (CreateWrite (dir, fn) data)) tid
      (mk_state fs lock dirs)
      false
      (mk_state fs lock dirs)
      nil
  | StepCreateWriteErr2 : forall fs tid dir fn data data' lock u P dirs,
    xstep (Slice (exist _ u P) (CreateWrite (dir, fn) data)) tid
      (mk_state fs lock dirs)
      false
      (mk_state (FMap.add (u, dir, fn) data' fs) lock dirs)
      nil
  | StepUnlink : forall fs tid dir fn lock u P dirs,
    xstep (Slice (exist _ u P) (Unlink (dir, fn))) tid
      (mk_state fs lock dirs)
      tt
      (mk_state (FMap.remove (u, dir, fn) fs) lock dirs)
      nil
  | StepLinkOK : forall fs tid srcdir srcfn data dstdir dstfn lock u P dirs,
    FMap.MapsTo (u, srcdir, srcfn) data fs ->
    ~ FMap.In (u, dstdir, dstfn) fs ->
    xstep (Slice (exist _ u P) (Link (srcdir, srcfn) (dstdir, dstfn))) tid
      (mk_state fs lock dirs)
      true
      (mk_state (FMap.add (u, dstdir, dstfn) data fs) lock dirs)
      nil
  | StepLinkErr : forall fs tid srcdir srcfn dstdir dstfn lock u P dirs,
    xstep (Slice (exist _ u P) (Link (srcdir, srcfn) (dstdir, dstfn))) tid
      (mk_state fs lock dirs)
      false
      (mk_state fs lock dirs)
      nil

  | StepList : forall fs tid r dirname lock u P dirs,
    FMap.is_permutation_key r (drop_dirname (filter_dir (u, dirname) fs)) ->
    xstep (Slice (exist _ u P) (List dirname)) tid
      (mk_state fs lock dirs)
      r
      (mk_state fs lock dirs)
      nil

  | StepDirOpen : forall fs lock dirs tid r dirname u P,
    ~ FMap.In r dirs ->
    xstep (Slice (exist _ u P) (DirOpen dirname)) tid
      (mk_state fs lock dirs)
      r
      (mk_state fs lock (FMap.add r ((u, dirname), FSet.empty) dirs))
      nil
  | StepDirNext : forall fs lock dirs dirname dirnames tid h name u P,
    FMap.MapsTo h (dirname, dirnames) dirs ->
    FMap.In (dirname, name) fs ->
    ~ FMap.In name dirnames ->
    xstep (Slice (exist _ u P) (DirNext h)) tid
      (mk_state fs lock dirs)
      (Some name)
      (mk_state fs lock (FMap.add h (dirname, FSet.add name dirnames) dirs))
      nil
  | StepDirNextEOF : forall fs lock dirs dirname dirnames tid h u P,
    FMap.MapsTo h (dirname, dirnames) dirs ->
    (forall name, FMap.In (dirname, name) fs -> FMap.In name dirnames) ->
    xstep (Slice (exist _ u P) (DirNext h)) tid
      (mk_state fs lock dirs)
      None
      (mk_state fs lock dirs)
      nil
  | StepDirClose : forall fs lock dirs tid h u P,
    xstep (Slice (exist _ u P) (DirClose h)) tid
      (mk_state fs lock dirs)
      tt
      (mk_state fs lock (FMap.remove h dirs))
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

  | StepReadOK : forall dir fn fs tid m lock u P dirs,
    FMap.MapsTo (u, dir, fn) m fs ->
    xstep (Slice (exist _ u P) (Read (dir, fn))) tid
      (mk_state fs lock dirs)
      (Some m)
      (mk_state fs lock dirs)
      nil
  | StepReadNone : forall dir fn fs tid lock u P dirs,
    ~ FMap.In (u, dir, fn) fs ->
    xstep (Slice (exist _ u P) (Read (dir, fn))) tid
      (mk_state fs lock dirs)
      None
      (mk_state fs lock dirs)
      nil

  | StepLock : forall fs tid u locked P dirs,
    FMap.MapsTo u false locked ->
    xstep (Slice (exist _ u P) Lock) tid
      (mk_state fs locked dirs)
      tt
      (mk_state fs (FMap.add u true locked) dirs)
      nil
  | StepLockErr : forall fs tid u locked P dirs,
    ~ FMap.In u locked ->
    xstep (Slice (exist _ u P) Lock) tid
      (mk_state fs locked dirs)
      tt
      (mk_state fs locked dirs)
      nil
  | StepUnlock : forall fs tid u locked P dirs,
    xstep (Slice (exist _ u P) Unlock) tid
      (mk_state fs locked dirs)
      tt
      (mk_state fs (FMap.add u false locked) dirs)
      nil

  | StepExistsOK : forall fs tid u P locked dirs,
    FMap.In u locked ->
    xstep (CheckSlice u) tid
      (mk_state fs locked dirs)
      (Present (exist _ u P))
      (mk_state fs locked dirs)
      nil
  | StepExistsErr : forall fs tid u locked dirs,
    ~ FMap.In u locked ->
    xstep (CheckSlice u) tid
      (mk_state fs locked dirs)
      Missing
      (mk_state fs locked dirs)
      nil

  | StepExt : forall s tid `(extop : extopT T) r u P,
    xstep (Slice (exist _ u P) (Ext extop)) tid
      s
      r
      s
      (Event (extop, r) :: nil)
  .

  Definition step := xstep.

End MailFSMergedAbsAPI.
