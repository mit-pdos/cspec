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

Require Import MailFSMergedAPI.
Require Import MailFSMergedImpl.

Require Import MailServerComposedAPI.
Require Import MailServerComposedImpl.


Import MailServerOp.
Import MailServerComposedOp.


Definition do_smtp_req : proc _ unit :=
  conn <- Call (Ext AcceptSMTP);
  omsg <- Call (Ext (SMTPGetMessage conn));
  match omsg with
  | None => Ret tt
  | Some (user, msg) =>
    eok <- Call (CheckUser user);
    match eok with
    | Missing =>
      _ <- Call (Ext (SMTPRespond conn false));
      Ret tt
    | Present u =>
      ok <- Call (Deliver u msg);
      _ <- Call (Ext (SMTPRespond conn ok));
      Ret tt
    end
  end.

Definition handle_pop3_one conn (u : validIndexT UserIdx.indexValid) (msgs : list ((nat*nat) * string)) :=
  req <- Call (Ext (POP3GetRequest conn));
  match req with
  | POP3Stat =>
    _ <- Call (Ext (POP3RespondStat conn (Datatypes.length msgs)
                  (fold_left plus (map string_length (map snd msgs)) 0)));
    Ret false
  | POP3List =>
    _ <- Call (Ext (POP3RespondList conn (map string_length (map snd msgs))));
    Ret false
  | POP3Retr n =>
    _ <- Call (Ext (POP3RespondRetr conn (nth n (map snd msgs) tmp_string)));
    Ret false
  | POP3Delete n =>
    _ <- Call (Delete u (nth n (map fst msgs) (0, 0)));
    _ <- Call (Ext (POP3RespondDelete conn));
    Ret false
  | POP3Closed =>
    Ret true
  end.

Definition do_pop3_req : proc _ unit :=
  conn <- Call (Ext AcceptPOP3);
  ouser <- Call (Ext (POP3Authenticate conn));
  match ouser with
  | None => Ret tt
  | Some user =>
    eok <- Call (CheckUser user);
    match eok with
    | Missing =>
      _ <- Call (Ext (POP3RespondAuth conn false));
      Ret tt
    | Present u =>
      _ <- Call (Ext (POP3RespondAuth conn true));
      msgs <- Call (Pickup u);
      _ <- Until (fun done => done)
                 (fun _ => handle_pop3_one conn u msgs)
                 None;
      Ret tt
    end
  end.

Definition smtp_server_thread : proc _ unit :=
  Until (fun _ => false) (fun _ => do_smtp_req) None.

Definition pop3_server_thread : proc _ unit :=
  Until (fun _ => false) (fun _ => do_pop3_req) None.

Fixpoint SpawnN (n:nat) Op T (p:proc Op T) : proc Op unit :=
  match n with
  | 0 => Ret tt
  | S n' => Bind (Spawn p) (fun _ => SpawnN n' p)
  end.

Definition threads_from_proc Op T (p: proc Op T) : threads_state Op :=
  thread_from_list (existT _ T p :: nil).

Definition mail_server nsmtp npop3 : threads_state _ :=
  threads_from_proc
    (Bind (SpawnN nsmtp smtp_server_thread)
           (fun _ => SpawnN npop3 pop3_server_thread)).

Definition pop3_one (u : validIndexT UserIdx.indexValid) (msgs : list ((nat*nat) * string)) :=
  Until
    (fun l => match l with | nil => true | _ => false end)
    (fun l => match l with
      | None => Ret nil
      | Some l =>
        match l with
        | nil => Ret nil
        | msg :: l' =>
          _ <- Call (Delete u (fst msg));
          Ret l'
        end
      end)
    (Some msgs).

Definition do_pop3 : proc _ unit :=
  u <- Call (Ext PickUser);
  eok <- Call (CheckUser u);
  match eok with
  | Missing =>
    Ret tt
  | Present u =>
    msgs <- Call (Pickup u);
    _ <- pop3_one u msgs;
    Ret tt
  end.

Definition do_smtp msg : proc _ unit :=
  u <- Call (Ext PickUser);
  eok <- Call (CheckUser u);
  match eok with
  | Missing =>
    Ret tt
  | Present u =>
    ok <- Call (Deliver u msg);
    Ret tt
  end.

Definition do_pop_loop niter :=
  Until
    (fun x => if x == 0 then true else false)
    (fun x =>
      match x with
      | None => Ret 0
      | Some niter =>
        _ <- do_pop3;
        Ret (niter - 1)
      end)
    (Some niter).

Definition do_smtp_loop msg niter :=
  Until
    (fun x => if x == 0 then true else false)
    (fun x =>
      match x with
      | None => Ret 0
      | Some niter =>
        _ <- do_smtp msg;
        Ret (niter - 1)
      end)
    (Some niter).

Definition do_bench_loop msg nsmtpiter npop3iter niter :=
  Until
    (fun x => if x == 0 then true else false)
    (fun x =>
      match x with
      | None => Ret 0
      | Some niter =>
        _ <- if nsmtpiter == 0 then Ret 0 else do_smtp_loop msg nsmtpiter;
        _ <- if npop3iter == 0 then Ret 0 else do_pop_loop npop3iter;
        Ret (niter - 1)
      end)
    (Some niter).

Definition mail_perf nprocs niter nsmtpiter npop3iter : threads_state _ :=
  threads_from_proc
    (SpawnN nprocs (do_bench_loop bench_msg nsmtpiter npop3iter niter)).

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

Module c0 :=
  Link
    MailFSMergedOp       MailFSMergedState       MailFSMergedAPI
    MailServerHOp        MailServerHState        MailServerHAPI
    MailServerComposedOp MailServerComposedState MailServerComposedAPI
    c10 MailServerComposedImpl.

Definition ms_bottom nsmtp npop3 nsmtpiter npop3iter :=
  (* TODO: these aren't actually the arguments mail_perf takes *)
  thread_to_list (c0.compile_ts (mail_perf nsmtp npop3 nsmtpiter npop3iter)).

Definition ms_bottom_server nsmtp npop3 :=
  thread_to_list (c0.compile_ts (mail_server nsmtp npop3)).

Print Assumptions c0.compile_traces_match.
