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

Require Import TryDeliverImpl.

Require Import MailFSMergedAPI.
Require Import MailFSMergedImpl.

Require Import MailServerComposedAPI.
Require Import MailServerComposedImpl.


Import MailServerOp.
Import MailServerComposedOp.


Definition do_smtp_req : proc _ unit :=
  conn <- Op (Ext AcceptSMTP);
  omsg <- Op (Ext (SMTPGetMessage conn));
  match omsg with
  | None => Ret tt
  | Some (user, msg) =>
    eok <- Op (CheckUser user);
    match eok with
    | Missing =>
      _ <- Op (Ext (SMTPRespond conn false));
      Ret tt
    | Present u =>
      ok <- Op (Deliver u msg);
      _ <- Op (Ext (SMTPRespond conn ok));
      Ret tt
    end
  end.

Definition handle_pop3_one conn (u : validIndexT UserIdx.indexValid) (msgs : list ((nat*nat) * string)) :=
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
    _ <- Op (Delete u (nth n (map fst msgs) (0, 0)));
    _ <- Op (Ext (POP3RespondDelete conn));
    Ret false
  | POP3Closed =>
    Ret true
  end.

Definition do_pop3_req : proc _ unit :=
  conn <- Op (Ext AcceptPOP3);
  ouser <- Op (Ext (POP3Authenticate conn));
  match ouser with
  | None => Ret tt
  | Some user =>
    eok <- Op (CheckUser user);
    match eok with
    | Missing =>
      _ <- Op (Ext (POP3RespondAuth conn false));
      Ret tt
    | Present u =>
      _ <- Op (Ext (POP3RespondAuth conn true));
      msgs <- Op (Pickup u);
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

Definition mail_server nsmtp npop3 :=
  repeat (Proc smtp_server_thread) nsmtp ++
  repeat (Proc pop3_server_thread) npop3.



Fixpoint pop3_one (u : validIndexT UserIdx.indexValid) (msgs : list ((nat*nat) * string)) :=
  match msgs with
  | nil => Ret tt
  | msg :: msgs' =>
    _ <- Op (Delete u (fst msg));
    pop3_one u msgs'
  end.

Definition do_pop3 u : proc _ unit :=
    eok <- Op (CheckUser u);
    match eok with
    | Missing =>
      Ret tt
    | Present u =>
      msgs <- Op (Pickup u);
      _ <- pop3_one u msgs;
      Ret tt
    end.

Definition do_smtp u msg : proc _ unit :=
  eok <- Op (CheckUser u);
  match eok with
  | Missing =>
    Ret tt
  | Present u =>
    ok <- Op (Deliver u msg);
    Ret tt
  end.

Fixpoint do_pop_loop u niter :=
  match niter with
  | S niter' =>
    _ <- do_pop3 u;
    do_pop_loop u niter'
  | O =>
    Ret tt
  end.

Fixpoint do_smtp_loop u msg niter :=
  match niter with
  | S niter' =>
    _ <- do_smtp u msg;
    do_smtp_loop u msg niter'
  | O =>
    Ret tt
  end.

Definition mail_perf nsmtp npop3 nsmtpiter npop3iter :=
  repeat (Proc (do_smtp_loop "u1" "msg" nsmtpiter)) nsmtp ++
  repeat (Proc (do_pop_loop "u1" npop3iter)) npop3.

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

Module c45' :=
  Link
    MailFSHOp     MailboxTmpAbsHState MailFSHAPI
    DeliverHOp    MailboxTmpAbsHState DeliverHAPI
    MailServerHOp MailServerHState    MailServerHAPI
    TryDeliverImplH c3.

Module c6 :=
  Link
    MailFSHOp     MailFSStringAbsHState MailFSStringAbsHAPI
    MailFSHOp     MailboxTmpAbsHState   MailFSHAPI
    MailServerHOp MailServerHState      MailServerHAPI
    MailFSStringAbsImplH
    (* c5 *)
    c45'.

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
  c0.compile_ts (mail_perf nsmtp npop3 nsmtpiter npop3iter).

Definition ms_bottom_smtp :=
  c0.compile_ts (Proc (do_smtp "u1"%string "msg"%string) :: nil).


Definition ms_bottom_server nsmtp npop3 :=
  c0.compile_ts (mail_server nsmtp npop3).

Print Assumptions c0.compile_traces_match.


Lemma exec_equiv_ts_build :
  forall opT `(p1 : proc opT T1) p2,
    exec_equiv p1 p2 ->
    exec_equiv_ts (Proc p1 :: nil) (Proc p2 :: nil).
Proof.
  unfold exec_equiv, exec_equiv_opt.
  intros.
  specialize (H (NoProc :: nil) 0).
  cbn in H.
  eauto.
Qed.

Lemma exec_equiv_until_proper :
  forall opT `(p1 : _ -> proc opT T) p2 c i,
    (forall x, exec_equiv_rx (p1 x) (p2 x)) ->
    exec_equiv_rx (Until c p1 i) (Until c p2 i).
Proof.
Admitted.

Lemma exec_equiv_rx_Some :
  forall opT `(p : T1 -> proc opT T2) x p',
    exec_equiv_rx ((fun ox => match ox with
                              | Some xx => p xx
                              | None => p'
                              end) (Some x)) (p x).
Proof.
  reflexivity.
Qed.

Lemma exec_equiv_rx_true :
  forall opT `(pt : proc opT T2) pf,
    exec_equiv_rx ((fun b => match b with
                             | true => pt
                             | false => pf
                             end) true) pt.
Proof.
  reflexivity.
Qed.

Lemma exec_equiv_rx_Present :
  forall opT `(P : TP -> Prop) `(p : validIndexT P -> proc opT T2) x p',
    exec_equiv_rx ((fun ox => match ox with
                              | Present xx => p xx
                              | Missing => p'
                              end) (Present x)) (p x).
Proof.
  reflexivity.
Qed.

Lemma exec_equiv_rx_pair :
  forall opT `(p : T1 -> T2 -> proc opT T3) x y,
    exec_equiv_rx ((fun '(xx, yy) => p xx yy) (x, y)) (p x y).
Proof.
  reflexivity.
Qed.

Lemma exec_equiv_rx_exist :
  forall opT `(P : T -> Prop) `(p : forall (x : T), P x -> proc opT T3) x y,
    exec_equiv_rx ((fun '(exist _ xx yy) => p xx yy) (exist P x y)) (p x y).
Proof.
  reflexivity.
Qed.

Ltac reflexivity' :=
  match goal with
  | |- exec_equiv_rx (?lhs ?a) (?rhs) =>
    let lhs' := eval pattern a in rhs in
    match lhs' with
    | ?f a => instantiate (1 := f); reflexivity
    end
  end.

(*
Definition ms_bottom' : {t : threads_state | exec_equiv_ts t (ms_bottom 1 0)}.
  cbn.
  eexists.
  eapply exec_equiv_ts_build.
  eapply exec_equiv_rx_to_exec_equiv.
  destruct nouser.
  eapply exec_equiv_until_proper; intros.
  eapply Bind_exec_equiv_proper; [ reflexivity | intro ].
  eapply Bind_exec_equiv_proper; [ reflexivity | intro ].

  destruct a0; simpl.
  destruct p; simpl.
  rewrite exec_equiv_rx_Some; [ | shelve ].
  2: simpl; reflexivity.

  rewrite exec_equiv_rx_pair.
  eapply Bind_exec_equiv_proper; [ reflexivity | intro ].

  destruct a0; simpl; clear;
    destruct nouser; simpl; clear.

  2: rewrite exec_equiv_rx_Present; [ | shelve ].
  simpl.
  reflexivity.

  destruct v.
  rewrite exec_equiv_bind_bind.
  rewrite exec_equiv_bind_bind.

  rewrite exec_equiv_rx_exist.
  eapply Bind_exec_equiv_proper; [ reflexivity | intro ].

  etransitivity; [ | rewrite exec_equiv_bind_bind; reflexivity ].
  eapply Bind_exec_equiv_proper; [ reflexivity | intro ].

  etransitivity; [ | rewrite exec_equiv_ret_bind; reflexivity ].
  destruct a1; simpl.

  rewrite exec_equiv_rx_true; [ | shelve ].
  2: simpl.

  repeat rewrite exec_equiv_bind_bind.
  eapply Bind_exec_equiv_proper; [ reflexivity | intro ].
  etransitivity; [ | rewrite exec_equiv_bind_bind; reflexivity ].
  etransitivity; [ | rewrite exec_equiv_bind_bind; reflexivity ].
  eapply Bind_exec_equiv_proper; [ reflexivity | intro ].
  etransitivity; [ | rewrite exec_equiv_bind_bind; reflexivity ].
  eapply Bind_exec_equiv_proper; [ reflexivity | intro ].
  etransitivity; [ | rewrite exec_equiv_ret_bind; reflexivity ].
  etransitivity; [ | rewrite exec_equiv_ret_bind; reflexivity ].
  etransitivity; [ | rewrite exec_equiv_bind_bind; reflexivity ].
  etransitivity; [ | rewrite exec_equiv_bind_bind; reflexivity ].
  eapply Bind_exec_equiv_proper; [ reflexivity | intro ].
  etransitivity; [ | rewrite exec_equiv_bind_bind; reflexivity ].
  eapply Bind_exec_equiv_proper; [ reflexivity | intro ].
  etransitivity; [ | rewrite exec_equiv_ret_bind; reflexivity ].
  etransitivity; [ | rewrite exec_equiv_ret_bind; reflexivity ].
  eapply Bind_exec_equiv_proper; [ reflexivity | intro ].
  reflexivity'.

  etransitivity; [ | rewrite exec_equiv_bind_bind; reflexivity ].
  etransitivity; [ | rewrite exec_equiv_bind_bind; reflexivity ].
  eapply Bind_exec_equiv_proper; [ reflexivity | intro ].
  etransitivity; [ | rewrite exec_equiv_bind_bind; reflexivity ].
  eapply Bind_exec_equiv_proper; [ reflexivity | intro ].
  etransitivity; [ | rewrite exec_equiv_ret_bind; reflexivity ].
  etransitivity; [ | rewrite exec_equiv_ret_bind; reflexivity ].
  eapply Bind_exec_equiv_proper; [ reflexivity | intro ].

  reflexivity'.
Defined.

Definition ms_bottom_1_0_simpl := Eval compute in (proj1_sig ms_bottom').
Print ms_bottom_1_0_simpl.
*)