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


Import MailServerOp.


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

Definition smtp_server_thread : proc MailServerOp.opT unit :=
  Until (fun _ => false) (fun _ => do_smtp_req) None.

Definition pop3_server_thread : proc MailServerOp.opT unit :=
  Until (fun _ => false) (fun _ => do_pop3_req) None.

Definition mail_server nsmtp npop3 :=
  repeat (Proc smtp_server_thread) nsmtp ++
  repeat (Proc pop3_server_thread) npop3.


Module c1 :=
  Link
    MailboxOp    MailServerLockAbsState MailboxAPI
    MailServerOp MailServerLockAbsState MailServerLockAbsAPI
    MailServerOp MailServerState        MailServerAPI
    AtomicReader MailServerLockAbsImpl.
Module c2 :=
  Link
    MailboxOp    MailboxTmpAbsState     MailboxTmpAbsAPI
    MailboxOp    MailServerLockAbsState MailboxAPI
    MailServerOp MailServerState        MailServerAPI
    MailboxTmpAbsImpl c1.
Module c3 :=
  Link
    DeliverOp    MailboxTmpAbsState     DeliverAPI
    MailboxOp    MailboxTmpAbsState     MailboxTmpAbsAPI
    MailServerOp MailServerState        MailServerAPI
    AtomicDeliver c2.

Module c4 :=
  Link
    DeliverListTidOp MailboxTmpAbsState DeliverListTidAPI
    DeliverOp        MailboxTmpAbsState DeliverAPI
    MailServerOp     MailServerState    MailServerAPI
    DeliverListTidImpl c3.
Module c5 :=
  Link
    MailFSOp         MailboxTmpAbsState MailFSAPI
    DeliverListTidOp MailboxTmpAbsState DeliverListTidAPI
    MailServerOp     MailServerState    MailServerAPI
    MailFSImpl c4.

Module c4' :=
  Link
    TryDeliverOp MailboxTmpAbsState TryDeliverAPI
    DeliverOp    MailboxTmpAbsState DeliverAPI
    MailServerOp MailServerState    MailServerAPI
    LinkRetryImpl c3.
Module c5' :=
  Link
    MailFSOp     MailboxTmpAbsState MailFSAPI
    TryDeliverOp MailboxTmpAbsState TryDeliverAPI
    MailServerOp MailServerState    MailServerAPI
    TryDeliverImpl c4'.

(*
Module c6 :=
  Link
    MailFSOp     MailFSStringAbsState MailFSStringAbsAPI
    MailFSOp     MailboxTmpAbsState   MailFSAPI
    MailServerOp MailServerState      MailServerAPI
    MailFSStringAbsImpl c5.
*)
Module c6 :=
  Link
    MailFSOp     MailFSStringAbsState MailFSStringAbsAPI
    MailFSOp     MailboxTmpAbsState   MailFSAPI
    MailServerOp MailServerState      MailServerAPI
    MailFSStringAbsImpl c5'.

Module c7 :=
  Link
    MailFSStringOp MailFSStringAbsState MailFSStringAPI
    MailFSOp       MailFSStringAbsState MailFSStringAbsAPI
    MailServerOp   MailServerState      MailServerAPI
    MailFSStringImpl c6.
Module c8 :=
  Link
    MailFSStringOp MailFSPathAbsState   MailFSPathAbsAPI
    MailFSStringOp MailFSStringAbsState MailFSStringAPI
    MailServerOp   MailServerState      MailServerAPI
    MailFSPathAbsImpl c7.
Module c9 :=
  Link
    MailFSPathOp   MailFSPathAbsState MailFSPathAPI
    MailFSStringOp MailFSPathAbsState MailFSPathAbsAPI
    MailServerOp   MailServerState    MailServerAPI
    MailFSPathImpl c8.


Definition ms_bottom nsmtp npop3 :=
  c9.compile_ts (mail_server nsmtp npop3).

Print Assumptions c9.compile_traces_match.
