Require Import CSPEC.
Require Import MailServerAPI.
Require Import MailboxTmpAbsAPI.
Require Import MailFSAPI.


Parameter encode_tid_fn : nat -> nat -> string.
Parameter decode_tid_fn : string -> (nat * nat).
Axiom encode_decode_tid_fn : forall tid fn,
  decode_tid_fn (encode_tid_fn tid fn) = (tid, fn).

Theorem encode_tid_eq : forall t1 t2 n1 n2,
  encode_tid_fn t1 n1 = encode_tid_fn t2 n2 ->
  (t1, n1) = (t2, n2).
Proof.
  intros.
  rewrite <- encode_decode_tid_fn at 1.
  rewrite H.
  rewrite encode_decode_tid_fn.
  eauto.
Qed.

Theorem encode_tid_fn_injective :
  FMap.injective (fun '(tid, fn) => encode_tid_fn tid fn).
Proof.
  unfold FMap.injective; intros.
  destruct k1; destruct k2.
  contradict H.
  eapply encode_tid_eq; eauto.
Qed.

Hint Resolve encode_tid_fn_injective.


Module MailFSStringAbsState <: State.

  Definition dir_contents := FMap.t string string.

  Record state_rec := mk_state {
    tmpdir : dir_contents;
    maildir : dir_contents;
    locked : bool;
  }.

  Definition State := state_rec.
  Definition initP (s : State) := locked s = false /\
                              tmpdir s = FMap.empty /\
                              maildir s = FMap.empty.

End MailFSStringAbsState.
Module MailFSStringAbsHState := HState MailFSStringAbsState UserIdx.


Module MailFSStringAbsAPI <: Layer MailFSOp MailFSStringAbsState.

  Import MailFSOp.
  Import MailFSStringAbsState.

  Inductive xstep : forall T, Op T -> nat -> State -> T -> State -> list event -> Prop :=
  | StepCreateTmpOK : forall tmp mbox tid lock,
    xstep (CreateTmp) tid
      (mk_state tmp mbox lock)
      true
      (mk_state (FMap.add (encode_tid_fn tid 0) empty_string tmp) mbox lock)
      nil
  | StepCreateTmpErr : forall tmp mbox tid lock,
    xstep (CreateTmp) tid
      (mk_state tmp mbox lock)
      false
      (mk_state tmp mbox lock)
      nil
  | StepWriteTmpOK : forall tmp mbox tid data lock,
    FMap.MapsTo (encode_tid_fn tid 0) empty_string tmp ->
    xstep (WriteTmp data) tid
      (mk_state tmp mbox lock)
      true
      (mk_state (FMap.add (encode_tid_fn tid 0) data tmp) mbox lock)
      nil
  | StepWriteTmpErr1 : forall tmp mbox tid data lock,
    xstep (WriteTmp data) tid
      (mk_state tmp mbox lock)
      false
      (mk_state tmp mbox lock)
      nil
  | StepWriteTmpErr2 : forall tmp mbox tid data data' lock,
    FMap.MapsTo (encode_tid_fn tid 0) empty_string tmp ->
    xstep (WriteTmp data) tid
      (mk_state tmp mbox lock)
      false
      (mk_state (FMap.add (encode_tid_fn tid 0) data' tmp) mbox lock)
      nil
  | StepUnlinkTmp : forall tmp mbox tid lock,
    xstep (UnlinkTmp) tid
      (mk_state tmp mbox lock)
      tt
      (mk_state (FMap.remove (encode_tid_fn tid 0) tmp) mbox lock)
      nil
  | StepLinkMailOK : forall tmp mbox tid mailfn data lock,
    FMap.MapsTo (encode_tid_fn tid 0) data tmp ->
    ~ FMap.In (encode_tid_fn tid mailfn) mbox ->
    xstep (LinkMail mailfn) tid
      (mk_state tmp mbox lock)
      true
      (mk_state tmp (FMap.add (encode_tid_fn tid mailfn) data mbox) lock)
      nil
  | StepLinkMail : forall tmp mbox tid mailfn lock,
    xstep (LinkMail mailfn) tid
      (mk_state tmp mbox lock)
      false
      (mk_state tmp mbox lock)
      nil

  | StepList : forall tmp mbox tid r lock,
    FMap.is_permutation_key r mbox ->
    xstep List tid
      (mk_state tmp mbox lock)
      (map decode_tid_fn r)
      (mk_state tmp mbox lock)
      nil

  | StepGetTID : forall tmp mbox tid lock,
    xstep GetTID tid
      (mk_state tmp mbox lock)
      tid
      (mk_state tmp mbox lock)
      nil
  | StepRandom : forall tmp mbox tid r lock,
    xstep Random tid
      (mk_state tmp mbox lock)
      r
      (mk_state tmp mbox lock)
      nil

  | StepReadOK : forall fntid fn tmp mbox tid m lock,
    FMap.MapsTo (encode_tid_fn fntid fn) m mbox ->
    xstep (Read (fntid, fn)) tid
      (mk_state tmp mbox lock)
      (Some m)
      (mk_state tmp mbox lock)
      nil
  | StepReadNone : forall fntid fn tmp mbox tid lock,
    ~ FMap.In (encode_tid_fn fntid fn) mbox ->
    xstep (Read (fntid, fn)) tid
      (mk_state tmp mbox lock)
      None
      (mk_state tmp mbox lock)
      nil

  | StepDelete : forall fntid fn tmp mbox tid lock,
    xstep (Delete (fntid, fn)) tid
      (mk_state tmp mbox lock)
      tt
      (mk_state tmp (FMap.remove (encode_tid_fn fntid fn) mbox) lock)
      nil

  | StepLock : forall tmp mbox tid,
    xstep Lock tid
      (mk_state tmp mbox false)
      tt
      (mk_state tmp mbox true)
      nil
  | StepUnlock : forall tmp mbox tid lock,
    xstep Unlock tid
      (mk_state tmp mbox lock)
      tt
      (mk_state tmp mbox false)
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

End MailFSStringAbsAPI.
Module MailFSStringAbsHAPI := HLayer MailFSOp MailFSStringAbsState MailFSStringAbsAPI UserIdx.
