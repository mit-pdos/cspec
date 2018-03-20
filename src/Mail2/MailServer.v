Require Import POCS.
Require Import MailServerAPI.

Require Import MailServerLockAbsAPI.
Require Import MailServerLockAbsImpl.

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

Definition handle_smtp conn :=
  msg <- Op (Ext (SMTPGetMessage conn));
  ok <- Op (Deliver msg);
  _ <- Op (Ext (SMTPRespond conn ok));
  Ret tt.

Definition handle_pop3_one conn :=
  req <- Op (Ext (POP3GetRequest conn));
  match req with
  | POP3Delete id =>
    _ <- Op (Delete id);
    _ <- Op (Ext (POP3Ack conn));
    Ret false
  | POP3Closed =>
    Ret true
  end.

Definition handle_pop3 conn :=
  msgs <- Op (Pickup);
  _ <- Op (Ext (POP3ListMessages conn msgs));
  _ <- Until (fun done => done)
             (fun _ => handle_pop3_one conn)
             None;
  Ret tt.

Definition do_mail_req : proc opT unit :=
  newconn <- Op (Ext AcceptConn);
  match newconn with
  | SMTPConn c => handle_smtp c
  | POP3Conn c => handle_pop3 c
  end.

Definition mail_server_thread : proc MailServerAPI.opT unit :=
  Until (fun _ => false) (fun _ => do_mail_req) None.

Definition mail_server nproc :=
  repeat (Proc mail_server_thread) nproc.


Module c1 := Link MailboxAPI MailServerLockAbsAPI MailServerAPI
                  AtomicReader MailServerLockAbsImpl.
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


Definition ms_bottom nproc :=
  c9.compile_ts (mail_server nproc).

Print Assumptions c9.compile_traces_match.
