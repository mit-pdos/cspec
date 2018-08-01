Require Import CSPEC.
Require Import Spec.Equiv.Execution.
Require Import Morphisms.
Require Import FunctionalExtensionality.

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

(* TCB: these implementations are trusted as specifications for how the mail
server should operate. The proof guarantees that each of these operations
behaves (as far as external calls) as if the mail server operations had atomic
semantics as given in MailServerAPI, for any number of threads running mail
server code (that is, threads can call Pickup/Delete/Deliver in any way, not
just with the code below). *)

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

Definition ms_bottom nprocs niter nsmtpiter npop3iter :=
  thread_to_list (c0.compile_ts (mail_perf nprocs niter nsmtpiter npop3iter)).

Definition ms_bottom_server nsmtp npop3 :=
  thread_to_list (c0.compile_ts (mail_server nsmtp npop3)).

Print Assumptions c0.compile_traces_match.


(**
 * Generating optimized code.
 *)

Theorem compile_SpawnN :
  forall Op1 Op2 (compile_op : forall T, Op1 T -> proc Op2 T) n `(p : proc _ T),
    Compile.compile compile_op (SpawnN n p) =
    SpawnN n (Compile.compile compile_op p).
Proof.
  induction n; simpl; intros; eauto.
  f_equal.
  apply functional_extensionality; eauto.
Qed.

Section ReadListCompiled.

  Variable Op : Type -> Type.
  Variable Pnil : list ((nat*nat) * string) -> proc Op (list (nat * nat * string)).
  Variable Pcons : nat*nat -> proc Op (option string).

  Fixpoint read_list_compiled (l : list (nat*nat)) (r : list ((nat*nat) * string)) {struct l} :=
      match l with
      | nil =>
        Pnil r
      | fn :: l' =>
        m <- Pcons fn;
        match m with
        | None => read_list_compiled l' r
        | Some s => read_list_compiled l' (r ++ ((fn, s) :: nil))
        end
      end.

End ReadListCompiled.

Theorem read_list_compiled_start :
  forall l r,
    AtomicReader'.read_list l r =
    read_list_compiled
      (fun r => _ <- Call MailboxOp.Unlock; Ret r)
      (fun fn => Call (MailboxOp.Read fn))
      l r.
Proof.
  induction l; simpl; eauto; intros.
Qed.

Theorem compile_read_list_compiled :
  forall Op1 Op2
         (compile_op : forall T, Op1 T -> proc Op2 T) p1 p2 l r,
    Compile.compile compile_op (read_list_compiled p1 p2 l r) =
    read_list_compiled
      (fun r => Compile.compile compile_op (p1 r))
      (fun fn => Compile.compile compile_op (p2 fn))
      l r.
Proof.
  induction l; simpl; eauto; intros.
  f_equal.
  apply functional_extensionality; intros.
  destruct x; eauto.
Qed.

Theorem read_list_compiled_proper :
  forall Op State p1 p1' p2 p2' l r (op_step : OpSemantics Op State),
    (forall r, exec_equiv_rx op_step (p1' r) (p1 r)) ->
    (forall fn, exec_equiv_rx op_step (p2' fn) (p2 fn)) ->
    exec_equiv_rx op_step (read_list_compiled p1' p2' l r) (read_list_compiled p1 p2 l r).
Proof.
  induction l; simpl; eauto; intros.
  rewrite H0.
  eapply exec_equiv_rx_bind_a; intros.
  destruct x; eauto.
Qed.

(* Optimize stuff. *)
Ltac reflexivity_maybe_fun :=
  reflexivity ||
  ( instantiate (1 := fun _ => _); reflexivity ).

Ltac step :=
  match goal with
  | _ => progress simpl; idtac "simpl"
  (* Fixpoints where [simpl] is not sufficient. *)
  | |- context[SpawnN] => rewrite compile_SpawnN; idtac "compile SpawnN"
  | |- context[MailboxImpl.AtomicReader'.read_list] => rewrite read_list_compiled_start; idtac "read_list_compiled_start"
  | |- context[read_list_compiled] => rewrite compile_read_list_compiled; idtac "compile_read_list_compiled"
  (* SliceProc is a wrapper around compilation; unfold it. *)
  | |- context[SliceProc] => unfold SliceProc; idtac "unfold SliceProc"
  (* Bubble up common program structures. *)
  | |- exec_equiv _ _ _ => eapply exec_equiv_rx_to_exec_equiv; idtac "exec_equiv_rx"
  | |- exec_equiv_rx _ _ (Bind (Bind _ _) _) => rewrite exec_equiv_rx_bind_bind; idtac "Bind Bind"
  | |- exec_equiv_rx _ _ (Bind (Ret _) _) => rewrite exec_equiv_ret_bind; idtac "Bind Ret"
  | |- exec_equiv_rx _ _ (Bind (Until _ _ _) _) => rewrite exec_equiv_until_once; idtac "Until once in Bind"
  | |- exec_equiv_rx _ _ (Bind _ _) => eapply Bind_exec_equiv_proper; idtac "Bind"
  | |- exec_equiv_rx _ _ (SpawnN _ _) => eapply SpawnN_exec_equiv_proper; [ reflexivity | ]; idtac "SpawnN"
  | |- exec_equiv_rx _ _ (Until _ _ _) => rewrite exec_equiv_until_once; idtac "Until once"
  | |- exec_equiv_rx _ _ (Until _ _ _) => eapply Until_exec_equiv_proper; [ reflexivity_maybe_fun | | reflexivity ]; idtac "Until"
  | |- exec_equiv_rx _ _ (read_list_compiled _ _ _ _) => eapply read_list_compiled_proper; intros; idtac "read_list_compiled"
  (* No more simplifications for [Call] and [Ret]. *)
  | |- exec_equiv_rx _ _ (Call _) => reflexivity; idtac "Call"
  | |- exec_equiv_rx _ _ (Ret _) => reflexivity; idtac "Ret"
  (* Create variables for continuation arguments, if necessary. *)
  | |- pointwise_relation _ _ _ _ => eapply pointwise_unused; idtac "Unused arg"
  | |- pointwise_relation _ _ _ _ => eapply pointwise_used; intros; idtac "Used arg"
  (* Create a [match ..] for things that depend on an argument. *)
  | |- exec_equiv_rx _ (_ ?arg) ?rhs =>
    match rhs with
    | context[match ?arg with _ => _ end] =>
      idtac "Match on" arg;
      (
        instantiate (1 := fun z => match z with | None => _ | Some a => _ a end) ||
        instantiate (1 := fun z => match z with | (a, b) => _ a b end) ||
        instantiate (1 := fun z => match z with | exist _ a _ => _ a end) ||
        instantiate (1 := fun z => match z with | Missing => _ | Present a => _ a end) ||
        instantiate (1 := fun z => match z with | true => _ | false => _ end) ||
        instantiate (1 := fun z => match z with | nil => _ | hd :: tl => _ hd tl end) ||
        instantiate (1 := fun z => match z with
          | MailServerAPI.MailServerOp.POP3Stat => _
          | MailServerAPI.MailServerOp.POP3List => _
          | MailServerAPI.MailServerOp.POP3Retr n => _ n
          | MailServerAPI.MailServerOp.POP3Delete n => _ n
          | MailServerAPI.MailServerOp.POP3Closed => _
          end) ||
        instantiate (1 := if arg then _ else _) ||
        ( idtac "Could not match on" arg; fail 1 )
      );
      idtac "Succeeded in building match on" arg;
      destruct arg
    | _ =>
      instantiate (1 := fun _ => _);
      idtac "Passing through argument" arg
    end
  end.

Definition ms_bottom_server_opt' a b :
    {ts : threads_state _ | exec_equiv_ts MailFSMergedAPI.step ts
                            (c0.compile_ts (mail_server a b))}.

  eexists.

  repeat eapply exec_equiv_ts_thread_map_thread_map.
  unfold compile.

  autorewrite with t.

  unfold mail_server.
  unfold threads_from_proc.
  rewrite thread_map_thread_from_list.
  cbn [map].

  eapply exec_equiv_ts_thread_from_list.

  eapply Forall2_cons.
  {
    do 3 eexists.
    split; [ reflexivity | ].
    split; [ reflexivity | ].

    repeat step.
  }

  eapply Forall2_nil.
Defined.

Definition ms_bottom_server_opt nsmtp npop3 :=
  Eval cbn in (thread_to_list (proj1_sig (ms_bottom_server_opt' nsmtp npop3))).

Print ms_bottom_server_opt.


Definition ms_bottom_opt' a b c d :
    {ts : threads_state _ | exec_equiv_ts MailFSMergedAPI.step ts
                            (c0.compile_ts (mail_perf a b c d))}.

  eexists.

  repeat eapply exec_equiv_ts_thread_map_thread_map.
  unfold compile.

  unfold mail_perf.
  unfold threads_from_proc.
  rewrite thread_map_thread_from_list.
  cbn [map].

  eapply exec_equiv_ts_thread_from_list.

  eapply Forall2_cons.
  {
    do 3 eexists.
    split; [ reflexivity | ].
    split; [ reflexivity | ].

    repeat step.
  }

  eapply Forall2_nil.
Defined.

Definition ms_bottom_opt a b c d :=
  Eval cbn in (thread_to_list (proj1_sig (ms_bottom_opt' a b c d))).

Print ms_bottom_opt.
