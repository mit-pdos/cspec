Require Import POCS.
Require Import String.


Parameter smtpconn : Type.
Parameter pop3conn : Type.

Module MailServerAPI <: Layer.

  Definition dir_contents := FMap.t (nat*nat) string.

  Inductive pop3req :=
  | POP3Stat
  | POP3List
  | POP3Retr : nat -> pop3req
  | POP3Delete : nat -> pop3req
  | POP3Closed
  .

  Inductive extopT : Type -> Type :=
  | AcceptSMTP : extopT smtpconn
  | SMTPGetMessage : smtpconn -> extopT (option string)
  | SMTPRespond : smtpconn -> bool -> extopT unit

  | AcceptPOP3 : extopT pop3conn
  | POP3GetRequest : pop3conn -> extopT pop3req
  | POP3RespondStat : pop3conn -> nat -> nat -> extopT unit
  | POP3RespondList : pop3conn -> list nat -> extopT unit
  | POP3RespondRetr : pop3conn -> string -> extopT unit
  | POP3RespondDelete : pop3conn -> extopT unit
  .

  Inductive xopT : Type -> Type :=
  | Deliver : forall (m : string), xopT bool
  | Pickup : xopT (list ((nat*nat) * string))
  | Delete : forall (id : nat*nat), xopT unit
  | Ext : forall `(op : extopT T), xopT T
  .

  Definition opT := xopT.
  Definition State := dir_contents.
  Definition initP (s : State) := True.

  Inductive xstep : forall T, opT T -> nat -> State -> T -> State -> list event -> Prop :=
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

  | StepExt : forall s tid `(extop : _ T) r,
    xstep (Ext extop) tid
      s
      r
      s
      (Event (extop, r) :: nil)
  .

  Definition step := xstep.

End MailServerAPI.
