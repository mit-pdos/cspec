Require Import POCS.
Require Import MailServerAPI.

Require Import MailServerDirAPI.
Require Import MailServerDirImpl.

Require Import MailboxAPI.
Require Import MailboxImpl.

Require Import MailboxTmpAbsAPI.
Require Import MailboxTmpAbsImpl.

Require Import DeliverAPI.
Require Import DeliverImpl.

Require Import DeliverListTidAPI.
Require Import DeliverListTidImpl.


Import MailServerAPI.

Definition do_mail_req : proc opT unit :=
  req <- Op GetRequest;
  match req with
  | ReqDeliver msg =>
    _ <- Op (Deliver msg);
    Op (Respond tt)
  | ReqRead =>
    msgs <- Op ReadAll;
    Op (Respond msgs)
  end.

Definition mail_server_thread : proc MailServerAPI.opT unit :=
  Until (fun _ => false) (fun _ => do_mail_req) tt.

Definition mail_server :=
  repeat (Proc mail_server_thread) 4.


Module c1 := Link MailboxAPI MailServerDirAPI MailServerAPI
                  AtomicReader MailServerDir.
Module c2 := Link MailboxTmpAbsAPI MailboxAPI MailServerAPI
                  MailboxTmpAbs c1.
Module c3 := Link DeliverAPI MailboxTmpAbsAPI MailServerAPI
                  AtomicDeliver c2.
Module c4 := Link DeliverListTidAPI DeliverAPI MailServerAPI
                  DeliverListTidImpl c3.


Definition ms_bottom := c4.compile_ts mail_server.
Check ms_bottom.

Print Assumptions c4.compile_traces_match.
