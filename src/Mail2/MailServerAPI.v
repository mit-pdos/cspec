Require Import POCS.
Require Import String.


Parameter smtpconn : Type.
Parameter pop3conn : Type.

Module MailServerAPI <: Layer.

  Definition dir_contents := FMap.t (nat*nat) string.

  Inductive newconn :=
  | SMTPConn : smtpconn -> newconn
  | POP3Conn : pop3conn -> newconn
  .

  Inductive pop3req :=
  | POP3Delete : nat*nat -> pop3req
  | POP3Closed : pop3req
  .

  Inductive extopT : Type -> Type :=
  | AcceptConn : extopT newconn
  | SMTPGetMessage : smtpconn -> extopT string
  | SMTPRespond : smtpconn -> bool-> extopT unit
  | POP3ListMessages : pop3conn -> list ((nat*nat) * string) -> extopT unit
  | POP3GetRequest : pop3conn -> extopT pop3req
  | POP3Ack : pop3conn -> extopT unit
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
