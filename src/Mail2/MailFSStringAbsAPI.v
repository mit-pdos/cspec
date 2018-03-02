Require Import POCS.
Require Import String.
Require Import MailServerAPI.
Require Import MailboxTmpAbsAPI.
Require Import MailFSAPI.


Parameter encode_tid_fn : nat -> string -> string.
Parameter decode_tid_fn : string -> (nat * string).
Axiom encode_decode_tid_fn : forall tid fn,
  decode_tid_fn (encode_tid_fn tid fn) = (tid, fn).


Module MailFSStringAbsAPI <: Layer.

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

  Definition dir_contents := FMap.t string string.

  Record state_rec := mk_state {
    tmpdir : dir_contents;
    maildir : dir_contents;
  }.

  Definition State := state_rec.
  Definition initP (s : State) := True.

  Inductive xstep : forall T, opT T -> nat -> State -> T -> State -> list event -> Prop :=
  | StepCreateTmp : forall tmp mbox tid fn,
    ~ FMap.In (encode_tid_fn tid fn) tmp ->
    xstep (CreateTmp) tid
      (mk_state tmp mbox)
      fn
      (mk_state (FMap.add (encode_tid_fn tid fn) ""%string tmp) mbox)
      nil
  | StepWriteTmp : forall tmp mbox tid fn data,
    FMap.In (encode_tid_fn tid fn) tmp ->
    xstep (WriteTmp fn data) tid
      (mk_state tmp mbox)
      tt
      (mk_state (FMap.add (encode_tid_fn tid fn) data tmp) mbox)
      nil
  | StepUnlinkTmp : forall tmp mbox tid fn,
    xstep (UnlinkTmp fn) tid
      (mk_state tmp mbox)
      tt
      (mk_state (FMap.remove (encode_tid_fn tid fn) tmp) mbox)
      nil
  | StepLinkMail : forall tmp mbox tid tmpfn mailfn data,
    FMap.MapsTo (encode_tid_fn tid tmpfn) data tmp ->
    ~ FMap.In (encode_tid_fn tid mailfn) mbox ->
    xstep (LinkMail tmpfn mailfn) tid
      (mk_state tmp mbox)
      tt
      (mk_state tmp (FMap.add (encode_tid_fn tid mailfn) data mbox))
      nil

  | StepList : forall tmp mbox tid r,
    FMap.is_permutation_key r mbox ->
    xstep List tid
      (mk_state tmp mbox)
      (map decode_tid_fn r)
      (mk_state tmp mbox)
      nil

  | StepGetTID : forall tmp mbox tid,
    xstep GetTID tid
      (mk_state tmp mbox)
      tid
      (mk_state tmp mbox)
      nil

  | StepRead : forall fntid fn tmp mbox tid m,
    FMap.MapsTo (encode_tid_fn fntid fn) m mbox ->
    xstep (Read (fntid, fn)) tid
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

End MailFSStringAbsAPI.
