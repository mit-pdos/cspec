Require Import POCS.
Require Import String.

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

Require Import MailFSMergedAPI.
Require Import MailFSMergedImpl.


Import MailServerOp.


Definition nouser := ""%string.

Definition do_smtp_req : proc _ unit :=
  conn <- Op (Slice nouser (Ext AcceptSMTP));
  omsg <- Op (Slice nouser (Ext (SMTPGetMessage conn)));
  match omsg with
  | None => Ret tt
  | Some (user, msg) =>
    ok <- Op (Slice user (Deliver msg));
    _ <- Op (Slice nouser (Ext (SMTPRespond conn ok)));
    Ret tt
  end.

Definition handle_pop3_one conn (u : string) (msgs : list ((nat*nat) * string)) :=
  req <- Op (Slice u (Ext (POP3GetRequest conn)));
  match req with
  | POP3Stat =>
    _ <- Op (Slice u (Ext (POP3RespondStat conn (Datatypes.length msgs)
                           (fold_left plus (map String.length (map snd msgs)) 0))));
    Ret false
  | POP3List =>
    _ <- Op (Slice u (Ext (POP3RespondList conn (map String.length (map snd msgs)))));
    Ret false
  | POP3Retr n =>
    _ <- Op (Slice u (Ext (POP3RespondRetr conn (nth n (map snd msgs) ""%string))));
    Ret false
  | POP3Delete n =>
    _ <- Op (Slice u (Delete (nth n (map fst msgs) (0, 0))));
    _ <- Op (Slice u (Ext (POP3RespondDelete conn)));
    Ret false
  | POP3Closed =>
    Ret true
  end.

Definition do_pop3_req : proc _ unit :=
  conn <- Op (Slice nouser (Ext AcceptPOP3));
  user <- Op (Slice nouser (Ext (POP3Authenticate conn)));
  msgs <- Op (Slice user Pickup);
  _ <- Until (fun done => done)
             (fun _ => handle_pop3_one conn user msgs)
             None;
  Ret tt.

Definition smtp_server_thread : proc _ unit :=
  Until (fun _ => false) (fun _ => do_smtp_req) None.

Definition pop3_server_thread : proc _ unit :=
  Until (fun _ => false) (fun _ => do_pop3_req) None.

Definition mail_server nsmtp npop3 :=
  repeat (Proc smtp_server_thread) nsmtp ++
  repeat (Proc pop3_server_thread) npop3.


Module c1 :=
  Link
    MailboxHOp    MailServerLockAbsHState MailboxHAPI
    MailServerHOp MailServerLockAbsHState MailServerLockAbsHAPI
    MailServerHOp MailServerHState        MailServerHAPI
    AtomicReaderH MailServerLockAbsImplH.
Module c2 :=
  Link
    MailboxHOp    MailboxTmpAbsHState     MailboxTmpAbsHAPI
    MailboxHOp    MailServerLockAbsHState MailboxHAPI
    MailServerHOp MailServerHState        MailServerHAPI
    MailboxTmpAbsImplH c1.
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


Module MailServerHOp := HOps MailServerOp StringIdx.
Module MailServerHState := HState MailServerState StringIdx.
Module MailServerHAPI := HLayer MailServerOp MailServerState MailServerAPI StringIdx.


Module c10 :=
  Link
    MailFSMergedOp MailFSMergedState MailFSMergedAPI
    MailFSHOp      MailFSHState      MailFSHPathAPI
    MailServerHOp  MailServerHState  MailServerHAPI
    MailFSMergedImpl ??.


Definition ms_bottom nsmtp npop3 :=
  c9.compile_ts (mail_server nsmtp npop3).

Print Assumptions c9.compile_traces_match.
