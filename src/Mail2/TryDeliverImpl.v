Require Import POCS.
Require Import String.
Require Import MailboxAPI.
Require Import TryDeliverAPI.
Require Import MailFSAPI.


Module TryDeliverImpl <: LayerImpl MailFSAPI TryDeliverAPI.

  Definition linkmail_core :=
    ts <- Op MailFSAPI.Random;
    ok <- Op (MailFSAPI.LinkMail ts);
    Ret ok.

  Definition compile_op T (op : TryDeliverAPI.opT T) : proc _ T :=
    match op with
    | TryDeliverAPI.CreateWriteTmp data => Op (MailFSAPI.CreateWriteTmp data)
    | TryDeliverAPI.LinkMail => linkmail_core
    | TryDeliverAPI.UnlinkTmp => Op (MailFSAPI.UnlinkTmp)
    | TryDeliverAPI.List => Op (MailFSAPI.List)
    | TryDeliverAPI.Read fn => Op (MailFSAPI.Read fn)
    | TryDeliverAPI.Delete fn => Op (MailFSAPI.Delete fn)
    | TryDeliverAPI.Lock => Op (MailFSAPI.Lock)
    | TryDeliverAPI.Unlock => Op (MailFSAPI.Unlock)
    | TryDeliverAPI.Ext extop => Op (MailFSAPI.Ext extop)
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
      (MailFSAPI.Random).
  Proof.
    unfold right_mover; intros.
    repeat step_inv; eauto 10.

    eexists; split; econstructor.
  Qed.

  Hint Resolve random_right_mover.

  Theorem linkmail_atomic : forall `(rx : _ -> proc _ T),
    trace_incl MailFSAPI.step
      (Bind (compile_op (TryDeliverAPI.LinkMail)) rx)
      (Bind (atomize compile_op (TryDeliverAPI.LinkMail)) rx).
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

  Definition absR (s1 : MailFSAPI.State) (s2 : TryDeliverAPI.State) :=
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
        MailFSAPI.initP
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
      MailFSAPI.initP s1 ->
      absR s1 s2 ->
      TryDeliverAPI.initP s2.
  Proof.
    eauto.
  Qed.

End TryDeliverImpl.
