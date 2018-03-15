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

  Definition createwritetmp_core data :=
    r <- Op (MailFSAPI.CreateWriteTmp data);
    Ret r.

  Definition unlinktmp_core :=
    r <- Op (MailFSAPI.UnlinkTmp);
    Ret r.

  Definition list_core :=
    l <- Op (MailFSAPI.List);
    Ret l.

  Definition read_core fn :=
    r <- Op (MailFSAPI.Read fn);
    Ret r.

  Definition getrequest_core :=
    r <- Op (MailFSAPI.GetRequest);
    Ret r.

  Definition respond_core T (r : T) :=
    r <- Op (MailFSAPI.Respond r);
    Ret r.

  Definition compile_op T (op : TryDeliverAPI.opT T) : proc _ T :=
    match op with
    | TryDeliverAPI.CreateWriteTmp data => createwritetmp_core data
    | TryDeliverAPI.LinkMail => linkmail_core
    | TryDeliverAPI.UnlinkTmp => unlinktmp_core
    | TryDeliverAPI.List => list_core
    | TryDeliverAPI.Read fn => read_core fn
    | TryDeliverAPI.GetRequest => getrequest_core
    | TryDeliverAPI.Respond r => respond_core r
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

  Theorem list_atomic : forall `(rx : _ -> proc _ T),
    trace_incl MailFSAPI.step
      (Bind (compile_op (TryDeliverAPI.List)) rx)
      (Bind (atomize compile_op (TryDeliverAPI.List)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold list_core, ysa_movers.
    eauto 20.
  Qed.

  Theorem read_atomic : forall `(rx : _ -> proc _ T) fn,
    trace_incl MailFSAPI.step
      (Bind (compile_op (TryDeliverAPI.Read fn)) rx)
      (Bind (atomize compile_op (TryDeliverAPI.Read fn)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold read_core, ysa_movers.
    eauto 20.
  Qed.

  Theorem createwritetmp_atomic : forall `(rx : _ -> proc _ T) data,
    trace_incl MailFSAPI.step
      (Bind (compile_op (TryDeliverAPI.CreateWriteTmp data)) rx)
      (Bind (atomize compile_op (TryDeliverAPI.CreateWriteTmp data)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold createwritetmp_core, ysa_movers.
    eauto 20.
  Qed.

  Theorem unlinktmp_atomic : forall `(rx : _ -> proc _ T),
    trace_incl MailFSAPI.step
      (Bind (compile_op (TryDeliverAPI.UnlinkTmp)) rx)
      (Bind (atomize compile_op (TryDeliverAPI.UnlinkTmp)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold unlinktmp_core, ysa_movers.
    eauto 20.
  Qed.

  Theorem getrequest_atomic : forall `(rx : _ -> proc _ T),
    trace_incl MailFSAPI.step
      (Bind (compile_op (TryDeliverAPI.GetRequest)) rx)
      (Bind (atomize compile_op (TryDeliverAPI.GetRequest)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold getrequest_core, ysa_movers.
    eauto 20.
  Qed.

  Theorem respond_atomic : forall `(rx : _ -> proc _ T) Tr (r : Tr),
    trace_incl MailFSAPI.step
      (Bind (compile_op (TryDeliverAPI.Respond r)) rx)
      (Bind (atomize compile_op (TryDeliverAPI.Respond r)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold respond_core, ysa_movers.
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
    destruct op.
    + rewrite createwritetmp_atomic.
      eapply trace_incl_bind_a; eauto.
    + rewrite linkmail_atomic.
      eapply trace_incl_bind_a; eauto.
    + rewrite unlinktmp_atomic.
      eapply trace_incl_bind_a; eauto.
    + rewrite list_atomic.
      eapply trace_incl_bind_a; eauto.
    + rewrite read_atomic.
      eapply trace_incl_bind_a; eauto.
    + rewrite getrequest_atomic.
      eapply trace_incl_bind_a; eauto.
    + rewrite respond_atomic.
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
