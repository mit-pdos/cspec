Require Import POCS.


Parameter smtpconn : Type.
Parameter pop3conn : Type.
Parameter abstract_string : Type.
Definition string: Type := abstract_string.
Parameter tmp_string : string.
Parameter mail_string : string.
Parameter bench_msg : string.
Parameter tmp_mail_ne : tmp_string <> mail_string.
Parameter abstract_string_length : string -> nat.
Definition string_length s := abstract_string_length s.

Instance string_Ordering : Ordering string.
Admitted.


Module UserIdx <: HIndex.
  Definition indexT := string.
  Parameter indexValid : string -> Prop.
  Definition indexCmp := string_Ordering.
End UserIdx.


Module MailServerOp <: Ops.

  Inductive pop3req :=
  | POP3Stat
  | POP3List
  | POP3Retr : nat -> pop3req
  | POP3Delete : nat -> pop3req
  | POP3Closed
  .

  Inductive extopT : Type -> Type :=
  | AcceptSMTP : extopT smtpconn
  | SMTPGetMessage : smtpconn -> extopT (option (string * string))
  | SMTPRespond : smtpconn -> bool -> extopT unit

  | AcceptPOP3 : extopT pop3conn
  | POP3Authenticate : pop3conn -> extopT (option string)
  | POP3RespondAuth : pop3conn -> bool -> extopT unit
  | POP3GetRequest : pop3conn -> extopT pop3req
  | POP3RespondStat : pop3conn -> nat -> nat -> extopT unit
  | POP3RespondList : pop3conn -> list nat -> extopT unit
  | POP3RespondRetr : pop3conn -> string -> extopT unit
  | POP3RespondDelete : pop3conn -> extopT unit

  (* For benchmarking *)
  | PickUser : extopT string
  .

  Inductive xOp : Type -> Type :=
  | Deliver : forall (m : string), xOp bool
  | Pickup : xOp (list ((nat*nat) * string))
  | Delete : forall (id : nat*nat), xOp unit
  | Ext : forall `(op : extopT T), xOp T
  .

  Definition Op := xOp.

End MailServerOp.
Module MailServerHOp := HOps MailServerOp UserIdx.


Module MailServerState <: State.

  Definition dir_contents := FMap.t (nat*nat) string.

  Definition State := dir_contents.
  Definition initP (s : State) := True.

End MailServerState.
Module MailServerHState := HState MailServerState UserIdx.


(* TCB: this is the top-level specification for the mail server. It specifies
what each operation does, and the proof covers any sequence of these
operations. *)
Module MailServerAPI <: Layer MailServerOp MailServerState.

  Import MailServerOp.
  Import MailServerState.

  Inductive xstep : forall T, Op T -> nat -> State -> T -> State -> list event -> Prop :=
  | StepDeliverOK : forall m mbox fn tid,
    ~ FMap.In fn mbox ->
    xstep (Deliver m) tid
      mbox
      true
      (FMap.add fn m mbox)
      nil
  | StepDeliverErr : forall m mbox tid,
    xstep (Deliver m) tid
      mbox
      false
      mbox
      nil
  | StepPickup : forall mbox tid r,
    FMap.is_permutation_kv r mbox ->
    xstep Pickup tid
      mbox
      r
      mbox
      nil
  | StepDelete : forall mbox tid id,
    xstep (Delete id) tid
      mbox
      tt
      (FMap.remove id mbox)
      nil

  | StepExt : forall s tid `(extop : extopT T) r,
    xstep (Ext extop) tid
      s
      r
      s
      (Event (extop, r) :: nil)
  .

  Definition step := xstep.

End MailServerAPI.
Module MailServerHAPI := HLayer MailServerOp MailServerState MailServerAPI UserIdx.
