Require Import POCS.
Require Import MailServerAPI.

Require Import MailboxAPI.
Require Import MailboxImpl.

Require Import MailboxTmpAbsAPI.
Require Import MailboxTmpAbsImpl.

Require Import DeliverAPI.
Require Import DeliverImpl.

Require Import DeliverListTidAPI.
Require Import DeliverListTidImpl.

Require Import MailFSAPI.
Require Import MailFSImpl.

Require Import MailFSStringAbsAPI.
Require Import MailFSStringAbsImpl.

Require Import MailFSStringAPI.
Require Import MailFSStringImpl.

Require Import MailFSPathAbsAPI.
Require Import MailFSPathAbsImpl.

Require Import MailFSPathAPI.
Require Import MailFSPathImpl.

Require Import LinkRetryImpl.

Require Import TryDeliverAPI.
Require Import TryDeliverImpl.


Import MailServerAPI.

Definition do_mail_req : proc opT unit :=
  req <- Op GetRequest;
  match req with
  | ReqDeliver msg =>
    _ <- Op (Deliver msg);
    Op (Respond tt)
  | ReqRead =>
    msgs <- Op Pickup;
    Op (Respond msgs)
  end.

Definition mail_server_thread : proc MailServerAPI.opT unit :=
  Until (fun _ => false) (fun _ => do_mail_req) tt.

Definition mail_server :=
  repeat (Proc mail_server_thread) 4.


Module c1 := AtomicReader.
Module c2 := Link MailboxTmpAbsAPI MailboxAPI MailServerAPI
                  MailboxTmpAbs c1.
Module c3 := Link DeliverAPI MailboxTmpAbsAPI MailServerAPI
                  AtomicDeliver c2.

Module c4 := Link DeliverListTidAPI DeliverAPI MailServerAPI
                  DeliverListTidImpl c3.
Module c5 := Link MailFSAPI DeliverListTidAPI MailServerAPI
                  MailFSImpl c4.

Module c4' := Link TryDeliverAPI DeliverAPI MailServerAPI
                  LinkRetryImpl c3.
Module c5' := Link MailFSAPI TryDeliverAPI MailServerAPI
                  TryDeliverImpl c4'.

(*
Module c6 := Link MailFSStringAbsAPI MailFSAPI MailServerAPI
                  MailFSStringAbsImpl c5.
*)
Module c6 := Link MailFSStringAbsAPI MailFSAPI MailServerAPI
                  MailFSStringAbsImpl c5'.

Module c7 := Link MailFSStringAPI MailFSStringAbsAPI MailServerAPI
                  MailFSStringImpl c6.
Module c8 := Link MailFSPathAbsAPI MailFSStringAPI MailServerAPI
                  MailFSPathAbsImpl c7.
Module c9 := Link MailFSPathAPI MailFSPathAbsAPI MailServerAPI
                  MailFSPathImpl c8.


Definition ms_bottom := c9.compile_ts mail_server.

Print Assumptions c9.compile_traces_match.
