Require Import POCS.
Require Import String.
Require Import MailServerAPI.
Require Import FMapFacts.


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
