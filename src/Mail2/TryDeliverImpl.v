Require Import POCS.
Require Import String.
Require Import MailboxAPI.
Require Import TryDeliverAPI.
Require Import MailFSAPI.
Require Import MailboxTmpAbsAPI.


Module TryDeliverImpl <:
  LayerImpl
    TryDeliverOp MailboxTmpAbsState TryDeliverAPI
    MailFSOp MailboxTmpAbsState MailFSAPI.

  Definition linkmail_core :=
    ts <- Op MailFSOp.Random;
    ok <- Op (MailFSOp.LinkMail ts);
    Ret ok.

  Definition compile_op T (op : TryDeliverOp.opT T) : proc _ T :=
    match op with
    | TryDeliverOp.CreateWriteTmp data => Op (MailFSOp.CreateWriteTmp data)
    | TryDeliverOp.LinkMail => linkmail_core
    | TryDeliverOp.UnlinkTmp => Op (MailFSOp.UnlinkTmp)
    | TryDeliverOp.List => Op (MailFSOp.List)
    | TryDeliverOp.Read fn => Op (MailFSOp.Read fn)
    | TryDeliverOp.Delete fn => Op (MailFSOp.Delete fn)
    | TryDeliverOp.Lock => Op (MailFSOp.Lock)
    | TryDeliverOp.Unlock => Op (MailFSOp.Unlock)
    | TryDeliverOp.Ext extop => Op (MailFSOp.Ext extop)
    end.

  Ltac step_inv :=
    match goal with
    | H : TryDeliverAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : MailFSAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    end; intuition idtac.

  Hint Extern 1 (TryDeliverAPI.step _ _ _ _ _ _) => econstructor.
  Hint Extern 1 (MailFSAPI.step _ _ _ _ _ _) => econstructor.

  Lemma random_right_mover :
    right_mover
      MailFSAPI.step
      (MailFSOp.Random).
  Proof.
    unfold right_mover; intros.
    repeat step_inv; eauto 10.

    eexists; split; econstructor.
  Qed.

  Hint Resolve random_right_mover.

  Theorem linkmail_atomic : forall `(rx : _ -> proc _ T),
    trace_incl MailFSAPI.step
      (Bind (compile_op (TryDeliverOp.LinkMail)) rx)
      (Bind (atomize compile_op (TryDeliverOp.LinkMail)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold linkmail_core, ysa_movers.
    eauto 20.
  Qed.

  Theorem my_compile_correct :
    compile_correct compile_op MailFSAPI.step TryDeliverAPI.step.
  Proof.
    unfold compile_correct; intros.
    destruct op.

    all: repeat atomic_exec_inv; repeat step_inv; eauto.
  Qed.

  Theorem my_atomize_correct :
    atomize_correct compile_op MailFSAPI.step.
  Proof.
    unfold atomize_correct; intros.
    destruct op; try trace_incl_simple.

    rewrite linkmail_atomic.
    eapply trace_incl_bind_a; eauto.
  Qed.

  Hint Resolve my_compile_correct.
  Hint Resolve my_atomize_correct.

  Theorem all_traces_match :
    forall ts1 ts2,
      proc_match (Compile.compile_ok compile_op) ts1 ts2 ->
      traces_match_ts MailFSAPI.step TryDeliverAPI.step ts1 ts2.
  Proof.
    intros.
    eapply Compile.compile_traces_match_ts; eauto.
  Qed.

  Definition absR (s1 : MailboxTmpAbsState.State) (s2 : MailboxTmpAbsState.State) :=
    s1 = s2.

  Definition compile_ts := Compile.compile_ts compile_op.

  Theorem compile_ts_no_atomics :
    forall ts,
      no_atomics_ts ts ->
      no_atomics_ts (compile_ts ts).
  Proof.
    eapply Compile.compile_ts_no_atomics.
    destruct op; compute; eauto.
  Qed.

  Theorem compile_traces_match :
    forall ts2,
      no_atomics_ts ts2 ->
      traces_match_abs absR
        MailboxTmpAbsState.initP
        MailFSAPI.step
        TryDeliverAPI.step (compile_ts ts2) ts2.
  Proof.
    unfold traces_match_abs; intros.
    rewrite H2 in *; clear H2.
    eapply all_traces_match; eauto.
    eapply Compile.compile_ts_ok; eauto.
  Qed.

  Theorem absInitP :
    forall s1 s2,
      MailboxTmpAbsState.initP s1 ->
      absR s1 s2 ->
      MailboxTmpAbsState.initP s2.
  Proof.
    eauto.
  Qed.

  Set Printing Implicit.
  
End TryDeliverImpl.
