Require Import POCS.
Require Import String.
Require Import MailServerAPI.
Require Import MailFSAPI.
Require Import MailFSStringAPI.
Require Import MailFSStringAbsAPI.


Module MailFSStringImpl <: LayerImpl MailFSStringAPI MailFSStringAbsAPI.

  Definition createwritetmp_core data :=
    tid <- Op (MailFSStringAPI.GetTID);
    r <- Op (MailFSStringAPI.CreateWriteTmp (encode_tid_fn tid 0) data);
    Ret r.

  Definition linkmail_core mboxfn :=
    tid <- Op (MailFSStringAPI.GetTID);
    v <- Op (MailFSStringAPI.LinkMail (encode_tid_fn tid 0) (encode_tid_fn tid mboxfn));
    Ret v.

  Definition unlinktmp_core :=
    tid <- Op (MailFSStringAPI.GetTID);
    r <- Op (MailFSStringAPI.UnlinkTmp (encode_tid_fn tid 0));
    Ret r.

  Definition gettid_core :=
    r <- Op (MailFSStringAPI.GetTID);
    Ret r.

  Definition random_core :=
    r <- Op (MailFSStringAPI.Random);
    Ret r.

  Definition list_core :=
    l <- Op (MailFSStringAPI.List);
    Ret (map decode_tid_fn l).

  Definition read_core (fn : nat*nat) :=
    r <- Op (MailFSStringAPI.Read (encode_tid_fn (fst fn) (snd fn)));
    Ret r.

  Definition getrequest_core :=
    r <- Op (MailFSStringAPI.GetRequest);
    Ret r.

  Definition respond_core T (r : T) :=
    r <- Op (MailFSStringAPI.Respond r);
    Ret r.

  Definition compile_op T (op : MailFSStringAbsAPI.opT T) : proc _ T :=
    match op with
    | MailFSAPI.LinkMail m => linkmail_core m
    | MailFSAPI.List => list_core
    | MailFSAPI.Read fn => read_core fn
    | MailFSAPI.CreateWriteTmp data => createwritetmp_core data
    | MailFSAPI.UnlinkTmp => unlinktmp_core
    | MailFSAPI.GetRequest => getrequest_core
    | MailFSAPI.Respond r => respond_core r
    | MailFSAPI.GetTID => gettid_core
    | MailFSAPI.Random => random_core
    end.

  Ltac step_inv :=
    match goal with
    | H : MailFSStringAbsAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : MailFSStringAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    end; intuition idtac.

  Hint Extern 1 (MailFSStringAbsAPI.step _ _ _ _ _ _) => econstructor.
  Hint Extern 1 (MailFSStringAPI.step _ _ _ _ _ _) => econstructor.

  Lemma gettid_right_mover :
    right_mover
      MailFSStringAPI.step
      (MailFSStringAPI.GetTID).
  Proof.
    unfold right_mover; intros.
    repeat step_inv; eauto.
  Qed.

  Hint Resolve gettid_right_mover.

  Theorem linkmail_atomic : forall `(rx : _ -> proc _ T) m,
    trace_incl MailFSStringAPI.step
      (Bind (compile_op (MailFSAPI.LinkMail m)) rx)
      (Bind (atomize compile_op (MailFSAPI.LinkMail m)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold linkmail_core, ysa_movers.
    eauto 20.
  Qed.

  Theorem list_atomic : forall `(rx : _ -> proc _ T),
    trace_incl MailFSStringAPI.step
      (Bind (compile_op (MailFSAPI.List)) rx)
      (Bind (atomize compile_op (MailFSAPI.List)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold list_core, ysa_movers.
    eauto 20.
  Qed.

  Theorem read_atomic : forall `(rx : _ -> proc _ T) fn,
    trace_incl MailFSStringAPI.step
      (Bind (compile_op (MailFSAPI.Read fn)) rx)
      (Bind (atomize compile_op (MailFSAPI.Read fn)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold read_core, ysa_movers.
    eauto 20.
  Qed.

  Theorem createwritetmp_atomic : forall `(rx : _ -> proc _ T) fn,
    trace_incl MailFSStringAPI.step
      (Bind (compile_op (MailFSAPI.CreateWriteTmp fn)) rx)
      (Bind (atomize compile_op (MailFSAPI.CreateWriteTmp fn)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold createwritetmp_core, ysa_movers.
    eauto 20.
  Qed.

  Theorem unlinktmp_atomic : forall `(rx : _ -> proc _ T),
    trace_incl MailFSStringAPI.step
      (Bind (compile_op (MailFSAPI.UnlinkTmp)) rx)
      (Bind (atomize compile_op (MailFSAPI.UnlinkTmp)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold unlinktmp_core, ysa_movers.
    eauto 20.
  Qed.

  Theorem gettid_atomic : forall `(rx : _ -> proc _ T),
    trace_incl MailFSStringAPI.step
      (Bind (compile_op (MailFSAPI.GetTID)) rx)
      (Bind (atomize compile_op (MailFSAPI.GetTID)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold gettid_core, ysa_movers.
    eauto 20.
  Qed.

  Theorem random_atomic : forall `(rx : _ -> proc _ T),
    trace_incl MailFSStringAPI.step
      (Bind (compile_op (MailFSAPI.Random)) rx)
      (Bind (atomize compile_op (MailFSAPI.Random)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold random_core, ysa_movers.
    eauto 20.
  Qed.

  Theorem getrequest_atomic : forall `(rx : _ -> proc _ T),
    trace_incl MailFSStringAPI.step
      (Bind (compile_op (MailFSAPI.GetRequest)) rx)
      (Bind (atomize compile_op (MailFSAPI.GetRequest)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold getrequest_core, ysa_movers.
    eauto 20.
  Qed.

  Theorem respond_atomic : forall `(rx : _ -> proc _ T) Tr (r : Tr),
    trace_incl MailFSStringAPI.step
      (Bind (compile_op (MailFSAPI.Respond r)) rx)
      (Bind (atomize compile_op (MailFSAPI.Respond r)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold respond_core, ysa_movers.
    eauto 20.
  Qed.

  Theorem my_compile_correct :
    compile_correct compile_op MailFSStringAPI.step MailFSStringAbsAPI.step.
  Proof.
    unfold compile_correct; intros.
    destruct op.

    all: try solve [ repeat atomic_exec_inv; repeat step_inv; eauto ].

    repeat atomic_exec_inv.
    repeat step_inv; eauto.
    simpl.

    destruct fn; simpl in *.
    eauto.
  Qed.

  Theorem my_atomize_correct :
    atomize_correct compile_op MailFSStringAPI.step.
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
    + rewrite random_atomic.
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
      traces_match_ts MailFSStringAPI.step MailFSStringAbsAPI.step ts1 ts2.
  Proof.
    intros.
    eapply Compile.compile_traces_match_ts; eauto.
  Qed.

  Definition absR (s1 : MailFSStringAPI.State) (s2 : MailFSStringAbsAPI.State) :=
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
        MailFSStringAPI.initP
        MailFSStringAPI.step
        MailFSStringAbsAPI.step (compile_ts ts2) ts2.
  Proof.
    unfold traces_match_abs; intros.
    rewrite H2 in *; clear H2.
    eapply all_traces_match; eauto.
    eapply Compile.compile_ts_ok; eauto.
  Qed.

  Theorem absInitP :
    forall s1 s2,
      MailFSStringAPI.initP s1 ->
      absR s1 s2 ->
      MailFSStringAbsAPI.initP s2.
  Proof.
    eauto.
  Qed.

End MailFSStringImpl.
