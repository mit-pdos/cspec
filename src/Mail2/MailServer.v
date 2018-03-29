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
    eok <- Op (CheckSlice user);
    match eok with
    | false =>
      _ <- Op (Slice nouser (Ext (SMTPRespond conn false)));
      Ret tt
    | true =>
      ok <- Op (Slice user (Deliver msg));
      _ <- Op (Slice nouser (Ext (SMTPRespond conn ok)));
      Ret tt
    end
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
  ouser <- Op (Slice nouser (Ext (POP3Authenticate conn)));
  match ouser with
  | None => Ret tt
  | Some user =>
    eok <- Op (CheckSlice user);
    _ <- Op (Slice nouser (Ext (POP3RespondAuth conn eok)));
    match eok with
    | false =>
      Ret tt
    | true =>
      msgs <- Op (Slice user Pickup);
      _ <- Until (fun done => done)
                 (fun _ => handle_pop3_one conn user msgs)
                 None;
      Ret tt
    end
  end.

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
    DeliverHOp    MailboxTmpAbsHState     DeliverHAPI
    MailboxHOp    MailboxTmpAbsHState     MailboxTmpAbsHAPI
    MailServerHOp MailServerHState        MailServerHAPI
    AtomicDeliverH c2.

Module c4 :=
  Link
    DeliverListTidHOp MailboxTmpAbsHState DeliverListTidHAPI
    DeliverHOp        MailboxTmpAbsHState DeliverHAPI
    MailServerHOp     MailServerHState    MailServerHAPI
    DeliverListTidImplH c3.
Module c5 :=
  Link
    MailFSHOp         MailboxTmpAbsHState MailFSHAPI
    DeliverListTidHOp MailboxTmpAbsHState DeliverListTidHAPI
    MailServerHOp     MailServerHState    MailServerHAPI
    MailFSImplH c4.

Module c4' :=
  Link
    TryDeliverHOp MailboxTmpAbsHState TryDeliverHAPI
    DeliverHOp    MailboxTmpAbsHState DeliverHAPI
    MailServerHOp MailServerHState    MailServerHAPI
    LinkRetryImplH c3.
Module c5' :=
  Link
    MailFSHOp     MailboxTmpAbsHState MailFSHAPI
    TryDeliverHOp MailboxTmpAbsHState TryDeliverHAPI
    MailServerHOp MailServerHState    MailServerHAPI
    TryDeliverImplH c4'.

Module c6 :=
  Link
    MailFSHOp     MailFSStringAbsHState MailFSStringAbsHAPI
    MailFSHOp     MailboxTmpAbsHState   MailFSHAPI
    MailServerHOp MailServerHState      MailServerHAPI
    MailFSStringAbsImplH
    (* c5 *)
    c5'.

Module c7 :=
  Link
    MailFSStringHOp MailFSStringAbsHState MailFSStringHAPI
    MailFSHOp       MailFSStringAbsHState MailFSStringAbsHAPI
    MailServerHOp   MailServerHState      MailServerHAPI
    MailFSStringImplH c6.
Module c8 :=
  Link
    MailFSStringHOp MailFSPathAbsHState   MailFSPathAbsHAPI
    MailFSStringHOp MailFSStringAbsHState MailFSStringHAPI
    MailServerHOp   MailServerHState      MailServerHAPI
    MailFSPathAbsImplH c7.
Module c9 :=
  Link
    MailFSPathHOp   MailFSPathAbsHState MailFSPathHAPI
    MailFSStringHOp MailFSPathAbsHState MailFSPathAbsHAPI
    MailServerHOp   MailServerHState    MailServerHAPI
    MailFSPathImplH c8.


Module c10 :=
  Link
    MailFSMergedOp MailFSMergedState   MailFSMergedAPI
    MailFSPathHOp  MailFSPathAbsHState MailFSPathHAPI
    MailServerHOp  MailServerHState    MailServerHAPI
    MailFSMergedImpl c9.


Definition ms_bottom nsmtp npop3 :=
  c10.compile_ts (mail_server nsmtp npop3).

Print Assumptions c10.compile_traces_match.
