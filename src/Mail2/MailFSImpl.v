Require Import POCS.
Require Import String.
Require Import MailServerAPI.
Require Import DeliverListTidAPI.
Require Import MailFSAPI.


Module MailFSImpl <: LayerImpl MailFSAPI DeliverListTidAPI.

  Definition same_tid (tid : nat) (fn : nat * string) : bool :=
    if tid == fst fn then
      true
    else
      false.

  Definition linkmail_core data :=
    v <- Op (MailFSAPI.LinkMail data);
    Ret v.

  Definition list_core :=
    l <- Op (MailFSAPI.List);
    Ret l.

  Definition listtid_core :=
    tid <- Op (MailFSAPI.GetTID);
    l <- Op (MailFSAPI.List);
    Ret (map snd (filter (same_tid tid) l)).

  Definition read_core fn :=
    r <- Op (MailFSAPI.Read fn);
    Ret r.

  Definition createwritetmp_core data :=
    r <- Op (MailFSAPI.CreateWriteTmp data);
    Ret r.

  Definition unlinktmp_core :=
    r <- Op (MailFSAPI.UnlinkTmp);
    Ret r.

  Definition getrequest_core :=
    r <- Op (MailFSAPI.GetRequest);
    Ret r.

  Definition respond_core T (r : T) :=
    r <- Op (MailFSAPI.Respond r);
    Ret r.

  Definition compile_op T (op : DeliverListTidAPI.opT T) : proc _ T :=
    match op with
    | DeliverListTidAPI.LinkMail m => linkmail_core m
    | DeliverListTidAPI.List => list_core
    | DeliverListTidAPI.ListTid => listtid_core
    | DeliverListTidAPI.Read fn => read_core fn
    | DeliverListTidAPI.CreateWriteTmp data => createwritetmp_core data
    | DeliverListTidAPI.UnlinkTmp => unlinktmp_core
    | DeliverListTidAPI.GetRequest => getrequest_core
    | DeliverListTidAPI.Respond r => respond_core r
    end.

  Ltac step_inv :=
    match goal with
    | H : MailFSAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : DeliverListTidAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    end; intuition idtac.

  Hint Extern 1 (MailFSAPI.step _ _ _ _ _ _) => econstructor.
  Hint Extern 1 (DeliverListTidAPI.step _ _ _ _ _ _) => econstructor.

  Lemma gettid_right_mover :
    right_mover
      MailFSAPI.step
      (MailFSAPI.GetTID).
  Proof.
    unfold right_mover; intros.
    repeat step_inv; eauto.
  Qed.

  Hint Resolve gettid_right_mover.

  Theorem linkmail_atomic : forall `(rx : _ -> proc _ T) m,
    trace_incl MailFSAPI.step
      (Bind (compile_op (DeliverListTidAPI.LinkMail m)) rx)
      (Bind (atomize compile_op (DeliverListTidAPI.LinkMail m)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold linkmail_core, ysa_movers.
    eauto 20.
  Qed.

  Theorem list_atomic : forall `(rx : _ -> proc _ T),
    trace_incl MailFSAPI.step
      (Bind (compile_op (DeliverListTidAPI.List)) rx)
      (Bind (atomize compile_op (DeliverListTidAPI.List)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold list_core, ysa_movers.
    eauto 20.
  Qed.

  Theorem listtid_atomic : forall `(rx : _ -> proc _ T),
    trace_incl MailFSAPI.step
      (Bind (compile_op (DeliverListTidAPI.ListTid)) rx)
      (Bind (atomize compile_op (DeliverListTidAPI.ListTid)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold listtid_core, ysa_movers.
    eauto 20.
  Qed.

  Theorem read_atomic : forall `(rx : _ -> proc _ T) fn,
    trace_incl MailFSAPI.step
      (Bind (compile_op (DeliverListTidAPI.Read fn)) rx)
      (Bind (atomize compile_op (DeliverListTidAPI.Read fn)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold read_core, ysa_movers.
    eauto 20.
  Qed.

  Theorem createwritetmp_atomic : forall `(rx : _ -> proc _ T) data,
    trace_incl MailFSAPI.step
      (Bind (compile_op (DeliverListTidAPI.CreateWriteTmp data)) rx)
      (Bind (atomize compile_op (DeliverListTidAPI.CreateWriteTmp data)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold createwritetmp_core, ysa_movers.
    eauto 20.
  Qed.

  Theorem unlinktmp_atomic : forall `(rx : _ -> proc _ T),
    trace_incl MailFSAPI.step
      (Bind (compile_op (DeliverListTidAPI.UnlinkTmp)) rx)
      (Bind (atomize compile_op (DeliverListTidAPI.UnlinkTmp)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold unlinktmp_core, ysa_movers.
    eauto 20.
  Qed.

  Theorem getrequest_atomic : forall `(rx : _ -> proc _ T),
    trace_incl MailFSAPI.step
      (Bind (compile_op (DeliverListTidAPI.GetRequest)) rx)
      (Bind (atomize compile_op (DeliverListTidAPI.GetRequest)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold getrequest_core, ysa_movers.
    eauto 20.
  Qed.

  Theorem respond_atomic : forall `(rx : _ -> proc _ T) Tr (r : Tr),
    trace_incl MailFSAPI.step
      (Bind (compile_op (DeliverListTidAPI.Respond r)) rx)
      (Bind (atomize compile_op (DeliverListTidAPI.Respond r)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold respond_core, ysa_movers.
    eauto 20.
  Qed.

  Theorem my_compile_correct :
    compile_correct compile_op MailFSAPI.step DeliverListTidAPI.step.
  Proof.
    unfold compile_correct; intros.
    destruct op.

    all: try solve [ repeat atomic_exec_inv; repeat step_inv; eauto ].

    repeat atomic_exec_inv.
    repeat step_inv; eauto.
    econstructor; intros.

(*
    split; intros.
    * eapply in_map_iff in H; deex. destruct x.
      eapply filter_In in H0; intuition idtac.
      unfold same_tid in *; simpl in *.
      destruct (v1 == n); try congruence.
      subst; eauto.
    * eapply in_map_iff.
      exists (v1, fn); intuition eauto.
      eapply filter_In; intuition eauto.
      unfold same_tid; simpl.
      destruct (v1 == v1); congruence.
  Qed.
*)
    admit.
  Admitted.

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
    + rewrite listtid_atomic.
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
      traces_match_ts MailFSAPI.step DeliverListTidAPI.step ts1 ts2.
  Proof.
    intros.
    eapply Compile.compile_traces_match_ts; eauto.
  Qed.

  Definition absR (s1 : MailFSAPI.State) (s2 : DeliverListTidAPI.State) :=
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
        DeliverListTidAPI.step (compile_ts ts2) ts2.
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
      DeliverListTidAPI.initP s2.
  Proof.
    eauto.
  Qed.

End MailFSImpl.
