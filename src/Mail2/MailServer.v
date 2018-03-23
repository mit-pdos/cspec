Require Import POCS.
Require Import String.

Require Import MailServerAPI.

Require Import MailServerHAPI.

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


Print MailServerHAPI.opT.


Definition do_smtp_req : proc opT unit :=
  conn <- Op (Ext AcceptSMTP);
  omsg <- Op (Ext (SMTPGetMessage conn));
  match omsg with
  | None => Ret tt
  | Some msg =>
    ok <- Op (Deliver msg);
    _ <- Op (Ext (SMTPRespond conn ok));
    Ret tt
  end.

Definition handle_pop3_one conn (msgs : list ((nat*nat) * string)) :=
  req <- Op (Ext (POP3GetRequest conn));
  match req with
  | POP3Stat =>
    _ <- Op (Ext (POP3RespondStat conn (Datatypes.length msgs)
                 (fold_left plus (map String.length (map snd msgs)) 0)));
    Ret false
  | POP3List =>
    _ <- Op (Ext (POP3RespondList conn (map String.length (map snd msgs))));
    Ret false
  | POP3Retr n =>
    _ <- Op (Ext (POP3RespondRetr conn (nth n (map snd msgs) ""%string)));
    Ret false
  | POP3Delete n =>
    _ <- Op (Delete (nth n (map fst msgs) (0, 0)));
    _ <- Op (Ext (POP3RespondDelete conn));
    Ret false
  | POP3Closed =>
    Ret true
  end.

Definition do_pop3_req : proc opT unit :=
  conn <- Op (Ext AcceptPOP3);
  msgs <- Op (Pickup);
  _ <- Until (fun done => done)
             (fun _ => handle_pop3_one conn msgs)
             None;
  Ret tt.

Definition smtp_server_thread : proc MailServerAPI.opT unit :=
  Until (fun _ => false) (fun _ => do_smtp_req) None.

Definition pop3_server_thread : proc MailServerAPI.opT unit :=
  Until (fun _ => false) (fun _ => do_pop3_req) None.

Definition mail_server nsmtp npop3 :=
  repeat (Proc smtp_server_thread) nsmtp ++
  repeat (Proc pop3_server_thread) npop3.


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


Definition ms_bottom nsmtp npop3 :=
  c9.compile_ts (mail_server nsmtp npop3).

Print Assumptions c9.compile_traces_match.
