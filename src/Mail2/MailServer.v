Require Import POCS.
Require Import MailServerAPI.

Require Import MailServerDirAPI.
Require Import MailServerDirImpl.

Require Import MailboxAPI.
Require Import MailboxImpl.


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


Module c := Link MailboxAPI MailServerDirAPI MailServerAPI
                 AtomicReader MailServerDir.


Definition ms_bottom := c.compile_ts mail_server.
Check ms_bottom.

Print Assumptions c.compile_traces_match.
