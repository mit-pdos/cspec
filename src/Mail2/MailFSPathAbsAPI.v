Require Import POCS.
Require Import String.
Require Import MailServerAPI.
Require Import MailFSStringAPI.


Module MailFSPathAbsAPI <: Layer.

  Import MailServerAPI.
  Import MailFSStringAPI.

  Definition opT := MailFSStringAPI.xopT.

  Definition fs_contents := FMap.t (string * string) string.

  Definition State := fs_contents.
  Definition initP (s : State) := True.

  Definition filter_dir (dirname : string) (fs : State) :=
    FMap.filter (fun '(dn, fn) => if string_dec dn dirname then true else false) fs.

  Definition drop_dirname (fs : State) :=
    FMap.map_keys (fun '(dn, fn) => fn) fs.

  Inductive xstep : forall T, opT T -> nat -> State -> T -> State -> list event -> Prop :=
  | StepCreateWriteTmp : forall fs tid tmpfn data,
    ~ FMap.In ("tmp"%string, tmpfn) fs ->
    xstep (CreateWriteTmp tmpfn data) tid
      fs
      tt
      (FMap.add ("tmp"%string, tmpfn) data fs)
      nil
  | StepUnlinkTmp : forall fs tid tmpfn,
    xstep (UnlinkTmp tmpfn) tid
      fs
      tt
      (FMap.remove ("tmp"%string, tmpfn) fs)
      nil
  | StepLinkMail : forall fs tid mailfn data tmpfn,
    FMap.MapsTo ("tmp"%string, tmpfn) data fs ->
    ~ FMap.In ("mail"%string, mailfn) fs ->
    xstep (LinkMail tmpfn mailfn) tid
      fs
      tt
      (FMap.add ("mail"%string, mailfn) data fs)
      nil

  | StepList : forall fs tid r,
    FMap.is_permutation_key r (drop_dirname (filter_dir "mail"%string fs)) ->
    xstep List tid
      fs
      r
      fs
      nil

  | StepGetTID : forall fs tid,
    xstep GetTID tid
      fs
      tid
      fs
      nil

  | StepRead : forall fn fs tid m,
    FMap.MapsTo ("mail"%string, fn) m fs ->
    xstep (Read fn) tid
      fs
      m
      fs
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
