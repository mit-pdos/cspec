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



Definition pop3_one (u : validIndexT UserIdx.indexValid) (msgs : list ((nat*nat) * string)) :=
  Until
    (fun l => match l with | nil => true | _ => false end)
    (fun l => match l with
      | None => Ret nil
      | Some l =>
        match l with
        | nil => Ret nil
        | msg :: l' =>
          _ <- Op (Delete u (fst msg));
          Ret l'
        end
      end)
    (Some msgs).

Definition do_pop3 : proc _ unit :=
  u <- Op (Ext PickUser);
  eok <- Op (CheckUser u);
  match eok with
  | Missing =>
    Ret tt
  | Present u =>
    msgs <- Op (Pickup u);
    _ <- pop3_one u msgs;
    Ret tt
  end.

Definition do_smtp msg : proc _ unit :=
  u <- Op (Ext PickUser);
  eok <- Op (CheckUser u);
  match eok with
  | Missing =>
    Ret tt
  | Present u =>
    ok <- Op (Deliver u msg);
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

Definition mail_perf nprocs niter nsmtpiter npop3iter :=
  repeat (Proc (do_bench_loop "msg" nsmtpiter npop3iter niter)) nprocs.

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
  c0.compile_ts (mail_perf nsmtp npop3 nsmtpiter npop3iter).

Definition ms_bottom_server nsmtp npop3 :=
  c0.compile_ts (mail_server nsmtp npop3).

Print Assumptions c0.compile_traces_match.


(*

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

Lemma exec_equiv_rx_nil :
  forall opT `(p : proc opT T) `(p' : LT -> list LT -> proc opT T),
    exec_equiv_rx ((fun l => match l with
                             | nil => p
                             | x :: l' => p' x l'
                             end) nil) p.
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


Section CompileTSHelper.

  Variable opT1 : Type -> Type.
  Variable opT2 : Type -> Type.
  Variable compile_proc : forall T, proc opT2 T -> proc opT1 T.

  Fixpoint compile_ts (ts : @threads_state opT2) : @threads_state opT1 :=
    match ts with
    | nil => nil
    | NoProc :: ts' => NoProc :: compile_ts ts'
    | Proc p :: ts' => Proc (compile_proc p) :: compile_ts ts'
    end.

End CompileTSHelper.

Theorem compile_ts_eq :
  forall `(compile_op : forall T, opT2 T -> proc opT1 T) ts,
    Compile.compile_ts compile_op ts =
    compile_ts (Compile.compile compile_op) ts.
Proof.
  induction ts; simpl; intros; eauto.
  destruct a; f_equal; eauto.
Qed.

Theorem compile_ts_loop_eq :
  forall `(compile_op : forall T, opT2 T -> (option T -> opT1 T) * (T -> bool) * option T) ts,
    CompileLoop.compile_ts compile_op ts =
    compile_ts (CompileLoop.compile _ compile_op) ts.
Proof.
  induction ts; simpl; intros; eauto.
  destruct a; f_equal; eauto.
Qed.

Theorem compile_ts_app :
  forall `(compile_proc : forall T, proc opT1 T -> proc opT2 T) ts1 ts2,
    compile_ts compile_proc (ts1 ++ ts2) =
    compile_ts compile_proc ts1 ++ compile_ts compile_proc ts2.
Proof.
  induction ts1; simpl; intros; eauto.
  destruct a; simpl; f_equal; eauto.
Qed.

Theorem compile_ts_compile_ts :
  forall `(compile_proc1 : forall T, proc opT1 T -> proc opT2 T)
         `(compile_proc2 : forall T, proc opT2 T -> proc opT3 T) ts,
    compile_ts compile_proc2 (compile_ts compile_proc1 ts) =
    compile_ts (fun T (p : proc opT1 T) => compile_proc2 _ (compile_proc1 _ p)) ts.
Proof.
  induction ts; simpl; intros; eauto.
  destruct a; simpl; f_equal; eauto.
Qed.

Theorem compile_ts_repeat :
  forall `(compile_proc : forall T, proc opT1 T -> proc opT2 T) p n,
    compile_ts compile_proc (repeat p n) =
    repeat (match p with
            | NoProc => NoProc
            | Proc p => Proc (compile_proc _ p)
            end) n.
Proof.
  induction n; simpl; intros; eauto.
  destruct p; f_equal; eauto.
Qed.

Theorem exec_equiv_ts_list' :
  forall opT (ts : @threads_state opT) ts' tsbase,
    Forall2 (fun p1 p2 =>
      exists T (p1' p2' : proc _ T),
        p1 = Proc p1' /\
        p2 = Proc p2' /\
        exec_equiv p1' p2') ts' ts ->
    exec_equiv_ts (tsbase ++ ts')
                  (tsbase ++ ts).
Proof.
  induction ts; destruct ts'; simpl; intros.
  - reflexivity.
  - inversion H.
  - inversion H.
  - inversion H; clear H; subst; repeat deex.
    unfold exec_equiv in H1.
    unfold exec_equiv_opt in H1.
    specialize (H1 (tsbase ++ Proc p1' :: ts') (Datatypes.length tsbase)).
    repeat rewrite thread_upd_app_length in H1.
    etransitivity; eauto.
    specialize (IHts ts' (tsbase ++ (Proc p2' :: nil))).
    intuition idtac.
    repeat rewrite <- app_assoc in H.
    simpl in *.
    eauto.
Qed.

Theorem exec_equiv_ts_list :
  forall opT (ts : @threads_state opT) ts',
    Forall2 (fun p1 p2 =>
      exists T (p1' p2' : proc _ T),
        p1 = Proc p1' /\
        p2 = Proc p2' /\
        exec_equiv p1' p2') ts' ts ->
    exec_equiv_ts ts' ts.
Proof.
  intros.
  pose proof (exec_equiv_ts_list').
  specialize (H0 _ ts ts' nil).
  eauto.
Qed.

Theorem Forall2_repeat :
  forall T (x y : T) (P : T -> T -> Prop) n,
    P x y ->
    Forall2 P (repeat x n) (repeat y n).
Proof.
  induction n; simpl; eauto.
Qed.


Definition ms_bottom_opt' nsmtp npop3 nsmtpiter npop3iter :
    {t : threads_state | exec_equiv_ts t (ms_bottom nsmtp npop3 nsmtpiter npop3iter)}.
  unfold ms_bottom.
  unfold mail_perf.
  unfold c0.compile_ts.
  unfold c10.compile_ts.
  unfold c9.compile_ts.
  unfold c8.compile_ts.
  unfold c7.compile_ts.
  unfold c6.compile_ts.
  unfold c5'.compile_ts.
  unfold c4'.compile_ts.
  unfold c3.compile_ts.
  unfold c2.compile_ts.
  unfold c1.compile_ts.
  unfold MailServerComposedImpl.compile_ts.
  unfold MailServerLockAbsImplH.compile_ts.
  unfold AtomicReaderH.compile_ts.
  unfold MailboxTmpAbsImplH.compile_ts.
  unfold AtomicDeliverH.compile_ts.
  unfold LinkRetryImplH.compile_ts.
  unfold TryDeliverImplH.compile_ts.
  unfold MailFSStringAbsImplH.compile_ts.
  unfold MailFSStringImplH.compile_ts.
  unfold MailFSPathAbsImplH.compile_ts.
  unfold MailFSPathImplH.compile_ts.
  unfold MailFSMergedImpl.compile_ts.
  unfold MailFSMergedOpImpl.compile_ts.
  unfold MailFSMergedAbsImpl.compile_ts.

  eexists.

  repeat rewrite compile_ts_eq.
  repeat rewrite compile_ts_loop_eq.
  repeat rewrite compile_ts_compile_ts.
  repeat rewrite compile_ts_app.
  repeat rewrite compile_ts_repeat.

  eapply exec_equiv_ts_list.
  eapply Forall2_app; eapply Forall2_repeat.

  - do 3 eexists.
    split; [ reflexivity | ].
    split; [ reflexivity | ].

    eapply exec_equiv_rx_to_exec_equiv.
    eapply exec_equiv_until_proper; intros.
    destruct x; simpl.
    rewrite exec_equiv_rx_Some; [ | shelve ].
    2: simpl; reflexivity.

    etransitivity; [ | rewrite exec_equiv_bind_bind; reflexivity ].
    etransitivity; [ | rewrite exec_equiv_until_once; reflexivity ].
    eapply Bind_exec_equiv_proper; [ reflexivity | intro ].

    etransitivity; [ | rewrite exec_equiv_bind_bind; reflexivity ].
    etransitivity; [ | rewrite exec_equiv_until_once; reflexivity ].
    eapply Bind_exec_equiv_proper; [ reflexivity | intro ].
    destruct a0; simpl.

    2: rewrite exec_equiv_rx_Present; [ | shelve ].
    simpl.
    etransitivity; [ | rewrite exec_equiv_ret_bind; reflexivity ].
    reflexivity.

    destruct v.
    rewrite exec_equiv_rx_exist.
    etransitivity; [ | rewrite exec_equiv_bind_bind; reflexivity ].
    etransitivity; [ | rewrite exec_equiv_bind_bind; reflexivity ].
    etransitivity; [ | rewrite exec_equiv_until_once; reflexivity ].
    etransitivity; [ | rewrite exec_equiv_bind_bind; reflexivity ].
    eapply Bind_exec_equiv_proper; [ reflexivity | intro ].

    etransitivity; [ | rewrite exec_equiv_bind_bind; reflexivity ].
    eapply Bind_exec_equiv_proper; [ reflexivity | intro ].

    etransitivity; [ | rewrite exec_equiv_ret_bind; reflexivity ].
    destruct a1; simpl.

    rewrite exec_equiv_rx_true; [ | shelve ].
    2: simpl.

    etransitivity; [ | rewrite exec_equiv_bind_bind; reflexivity ].
    etransitivity; [ | erewrite exec_equiv_until_proper; [ reflexivity | intros ] ].
    2: {
      eapply Bind_exec_equiv_proper; [ reflexivity | intro ].
      etransitivity; [ rewrite exec_equiv_bind_bind; reflexivity | ].
      eapply Bind_exec_equiv_proper; [ reflexivity | intro ].
      etransitivity; [ rewrite exec_equiv_bind_bind; reflexivity | ].
      eapply Bind_exec_equiv_proper; [ reflexivity | intro ].
      etransitivity; [ rewrite exec_equiv_ret_bind; reflexivity | ].
      reflexivity.
    }

    eapply Bind_exec_equiv_proper; [ reflexivity | intro ].

    etransitivity; [ | rewrite exec_equiv_bind_bind; reflexivity ].
    etransitivity; [ | rewrite exec_equiv_until_once; reflexivity ].
    etransitivity; [ | rewrite exec_equiv_bind_bind; reflexivity ].
    eapply Bind_exec_equiv_proper; [ reflexivity | intro ].

    etransitivity; [ | rewrite exec_equiv_bind_bind; reflexivity ].
    eapply Bind_exec_equiv_proper; [ reflexivity | intro ].

    etransitivity; [ | rewrite exec_equiv_ret_bind; reflexivity ].
    etransitivity; [ | rewrite exec_equiv_ret_bind; reflexivity ].
    etransitivity; [ | rewrite exec_equiv_ret_bind; reflexivity ].
    reflexivity'.

    etransitivity; [ | rewrite exec_equiv_until_once; reflexivity ].
    etransitivity; [ | rewrite exec_equiv_bind_bind; reflexivity ].
    etransitivity; [ | rewrite exec_equiv_bind_bind; reflexivity ].
    eapply Bind_exec_equiv_proper; [ reflexivity | intro ].

    etransitivity; [ | rewrite exec_equiv_bind_bind; reflexivity ].
    eapply Bind_exec_equiv_proper; [ reflexivity | intro ].

    etransitivity; [ | rewrite exec_equiv_ret_bind; reflexivity ].
    etransitivity; [ | rewrite exec_equiv_ret_bind; reflexivity ].
    etransitivity; [ | rewrite exec_equiv_ret_bind; reflexivity ].
    reflexivity'.

  - do 3 eexists.
    split; [ reflexivity | ].
    split; [ reflexivity | ].

    eapply exec_equiv_rx_to_exec_equiv.
    eapply exec_equiv_until_proper; intros.
    destruct x; simpl.
    rewrite exec_equiv_rx_Some; [ | shelve ].
    2: simpl; reflexivity.

    etransitivity; [ | rewrite exec_equiv_bind_bind; reflexivity ].
    etransitivity; [ | rewrite exec_equiv_until_once; reflexivity ].
    destruct nouser.
    eapply Bind_exec_equiv_proper; [ reflexivity | intro ].

    etransitivity; [ | rewrite exec_equiv_bind_bind; reflexivity ].
    etransitivity; [ | rewrite exec_equiv_until_once; reflexivity ].
    eapply Bind_exec_equiv_proper; [ reflexivity | intro ].
    destruct a0; simpl.

    2: rewrite exec_equiv_rx_Present; [ | shelve ].
    simpl.
    etransitivity; [ | rewrite exec_equiv_ret_bind; reflexivity ].
    reflexivity.

    destruct v.
    rewrite exec_equiv_rx_exist.
    etransitivity; [ | rewrite exec_equiv_bind_bind; reflexivity ].
    etransitivity; [ | rewrite exec_equiv_bind_bind; reflexivity ].
    etransitivity; [ | rewrite exec_equiv_until_once; reflexivity ].
    eapply Bind_exec_equiv_proper; [ reflexivity | intro ].

    etransitivity; [ | rewrite exec_equiv_bind_bind; reflexivity ].
    etransitivity; [ | rewrite exec_equiv_until_once; reflexivity ].
    etransitivity; [ | rewrite exec_equiv_bind_bind; reflexivity ].
    eapply Bind_exec_equiv_proper; [ reflexivity | intro ].

    reflexivity'.
Defined.

Definition ms_bottom_opt nsmtp npop3 nsmtpiter npop3iter :=
  Eval cbn in (proj1_sig (ms_bottom_opt' nsmtp npop3 nsmtpiter npop3iter)).
Print ms_bottom_opt.


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

*)
