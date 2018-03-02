Require Import POCS.
Require Import String.
Require Import MailServerAPI.
Require Import MailFSStringAPI.
Require Import MailFSPathAbsAPI.
Require Import MailFSPathAPI.


Module MailFSPathImpl <: LayerImpl MailFSPathAPI MailFSPathAbsAPI.

  Definition createwritetmp_core fn data :=
    r <- Op (MailFSPathAPI.CreateWrite ("tmp"%string, fn) data);
    Ret r.

  Definition linkmail_core tmpfn mboxfn :=
    v <- Op (MailFSPathAPI.Link ("tmp"%string, tmpfn) ("mail"%string, mboxfn));
    Ret v.

  Definition unlinktmp_core tmpfn :=
    r <- Op (MailFSPathAPI.Unlink ("tmp"%string, tmpfn));
    Ret r.

  Definition gettid_core :=
    r <- Op (MailFSPathAPI.GetTID);
    Ret r.

  Definition list_core :=
    l <- Op (MailFSPathAPI.List "mail"%string);
    Ret l.

  Definition read_core (fn : string) :=
    r <- Op (MailFSPathAPI.Read ("mail"%string, fn));
    Ret r.

  Definition getrequest_core :=
    r <- Op (MailFSPathAPI.GetRequest);
    Ret r.

  Definition respond_core T (r : T) :=
    r <- Op (MailFSPathAPI.Respond r);
    Ret r.

  Definition compile_op T (op : MailFSPathAbsAPI.opT T) : proc _ T :=
    match op with
    | MailFSStringAPI.LinkMail tmpfn mailfn => linkmail_core tmpfn mailfn
    | MailFSStringAPI.List => list_core
    | MailFSStringAPI.Read fn => read_core fn
    | MailFSStringAPI.CreateWriteTmp tmpfn data => createwritetmp_core tmpfn data
    | MailFSStringAPI.UnlinkTmp tmpfn => unlinktmp_core tmpfn
    | MailFSStringAPI.GetRequest => getrequest_core
    | MailFSStringAPI.Respond r => respond_core r
    | MailFSStringAPI.GetTID => gettid_core
    end.

  Ltac step_inv :=
    match goal with
    | H : MailFSPathAbsAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : MailFSPathAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    end; intuition idtac.

  Hint Extern 1 (MailFSPathAbsAPI.step _ _ _ _ _ _) => econstructor.
  Hint Extern 1 (MailFSPathAPI.step _ _ _ _ _ _) => econstructor.

  Theorem linkmail_atomic : forall `(rx : _ -> proc _ T) fn m,
    trace_incl MailFSPathAPI.step
      (Bind (compile_op (MailFSStringAPI.LinkMail fn m)) rx)
      (Bind (atomize compile_op (MailFSStringAPI.LinkMail fn m)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold linkmail_core, ysa_movers.
    eauto 20.
  Qed.

  Theorem list_atomic : forall `(rx : _ -> proc _ T),
    trace_incl MailFSPathAPI.step
      (Bind (compile_op (MailFSStringAPI.List)) rx)
      (Bind (atomize compile_op (MailFSStringAPI.List)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold list_core, ysa_movers.
    eauto 20.
  Qed.

  Theorem read_atomic : forall `(rx : _ -> proc _ T) fn,
    trace_incl MailFSPathAPI.step
      (Bind (compile_op (MailFSStringAPI.Read fn)) rx)
      (Bind (atomize compile_op (MailFSStringAPI.Read fn)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold read_core, ysa_movers.
    eauto 20.
  Qed.

  Theorem createwritetmp_atomic : forall `(rx : _ -> proc _ T) tmpfn data,
    trace_incl MailFSPathAPI.step
      (Bind (compile_op (MailFSStringAPI.CreateWriteTmp tmpfn data)) rx)
      (Bind (atomize compile_op (MailFSStringAPI.CreateWriteTmp tmpfn data)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold createwritetmp_core, ysa_movers.
    eauto 20.
  Qed.

  Theorem unlinktmp_atomic : forall `(rx : _ -> proc _ T) fn,
    trace_incl MailFSPathAPI.step
      (Bind (compile_op (MailFSStringAPI.UnlinkTmp fn)) rx)
      (Bind (atomize compile_op (MailFSStringAPI.UnlinkTmp fn)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold unlinktmp_core, ysa_movers.
    eauto 20.
  Qed.

  Theorem gettid_atomic : forall `(rx : _ -> proc _ T),
    trace_incl MailFSPathAPI.step
      (Bind (compile_op (MailFSStringAPI.GetTID)) rx)
      (Bind (atomize compile_op (MailFSStringAPI.GetTID)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold gettid_core, ysa_movers.
    eauto 20.
  Qed.

  Theorem getrequest_atomic : forall `(rx : _ -> proc _ T),
    trace_incl MailFSPathAPI.step
      (Bind (compile_op (MailFSStringAPI.GetRequest)) rx)
      (Bind (atomize compile_op (MailFSStringAPI.GetRequest)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold getrequest_core, ysa_movers.
    eauto 20.
  Qed.

  Theorem respond_atomic : forall `(rx : _ -> proc _ T) Tr (r : Tr),
    trace_incl MailFSPathAPI.step
      (Bind (compile_op (MailFSStringAPI.Respond r)) rx)
      (Bind (atomize compile_op (MailFSStringAPI.Respond r)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold respond_core, ysa_movers.
    eauto 20.
  Qed.

  Theorem my_compile_correct :
    compile_correct compile_op MailFSPathAPI.step MailFSPathAbsAPI.step.
  Proof.
    unfold compile_correct; intros.
    destruct op.

    all: try solve [ repeat atomic_exec_inv; repeat step_inv; eauto ].
  Qed.

  Theorem my_atomize_correct :
    atomize_correct compile_op MailFSPathAPI.step.
  Proof.
    unfold atomize_correct; intros.
    destruct op.
    + rewrite createwritetmp_atomic.
      eapply trace_incl_bind_a; eauto.
    + rewrite linkmail_atomic.
      eapply trace_incl_bind_a; eauto.
    + rewrite unlinktmp_atomic.
      eapply trace_incl_bind_a; eauto.
    + rewrite gettid_atomic.
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
      traces_match_ts MailFSPathAPI.step MailFSPathAbsAPI.step ts1 ts2.
  Proof.
    intros.
    eapply Compile.compile_traces_match_ts; eauto.
  Qed.

  Definition absR (s1 : MailFSPathAPI.State) (s2 : MailFSPathAbsAPI.State) :=
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
        MailFSPathAPI.initP
        MailFSPathAPI.step
        MailFSPathAbsAPI.step (compile_ts ts2) ts2.
  Proof.
    unfold traces_match_abs; intros.
    rewrite H2 in *; clear H2.
    eapply all_traces_match; eauto.
    eapply Compile.compile_ts_ok; eauto.
  Qed.

  Theorem absInitP :
    forall s1 s2,
      MailFSPathAPI.initP s1 ->
      absR s1 s2 ->
      MailFSPathAbsAPI.initP s2.
  Proof.
    eauto.
  Qed.

End MailFSPathImpl.
