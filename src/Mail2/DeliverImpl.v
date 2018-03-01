Require Import POCS.
Require Import String.
Require Import DeliverAPI.
Require Import MailboxAPI.
Require Import MailboxTmpAbsAPI.


Module AtomicDeliver <: LayerImpl DeliverAPI MailboxTmpAbsAPI.

  Definition deliver_core (m : string) :=
    tmpfn <- Op (DeliverAPI.CreateTmp);
    _ <- Op (DeliverAPI.WriteTmp tmpfn m);
    _ <- Op (DeliverAPI.LinkMail tmpfn);
    _ <- Op (DeliverAPI.UnlinkTmp tmpfn);
    Ret tt.

  Definition list_core :=
    l <- Op (DeliverAPI.List);
    Ret l.

  Definition read_core fn :=
    r <- Op (DeliverAPI.Read fn);
    Ret r.

  Definition getrequest_core :=
    r <- Op (DeliverAPI.GetRequest);
    Ret r.

  Definition respond_core T (v : T) :=
    r <- Op (DeliverAPI.Respond v);
    Ret r.

  Definition compile_op T (op : MailboxAPI.opT T) : proc _ T :=
    match op with
    | MailboxAPI.Deliver m => deliver_core m
    | MailboxAPI.List => list_core
    | MailboxAPI.Read fn => read_core fn
    | MailboxAPI.GetRequest => getrequest_core
    | MailboxAPI.Respond r => respond_core r
    end.

  Ltac step_inv :=
    match goal with
    | H : MailboxAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : MailboxTmpAbsAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : DeliverAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    end; intuition idtac.

  Hint Extern 1 (MailboxAPI.step _ _ _ _ _ _) => econstructor.
  Hint Extern 1 (MailboxTmpAbsAPI.step _ _ _ _ _ _) => econstructor.
  Hint Extern 1 (DeliverAPI.step _ _ _ _ _ _) => econstructor.

  Lemma createtmp_right_mover :
    right_mover
      DeliverAPI.step
      (DeliverAPI.CreateTmp).
  Proof.
    unfold right_mover; intros.
    repeat step_inv.
    - eexists; split.
      + econstructor.
        contradict H12.
        eapply FMap.in_add; eauto.
      + rewrite FMap.add_add_ne by congruence.
        econstructor.
        contradict H1.
        eapply FMap.in_add_ne; eauto.
        congruence.
    - eexists; split.
      + econstructor.
        eapply FMap.in_add_ne; eauto.
        congruence.
      + rewrite FMap.add_add_ne by congruence.
        econstructor.
        contradict H1.
        eapply FMap.in_add_ne; eauto.
        congruence.
    - eexists; split; eauto.
      rewrite <- FMap.add_remove_ne by congruence.
      econstructor.
      contradict H1.
      eapply FMap.in_remove; eauto.
    - eexists; split; eauto.
      econstructor; eauto.
      eapply FMap.mapsto_add_ne; eauto.
      congruence.
    - eauto 20.
    - eauto 20.
    - eauto 20.
    - eauto 20.
  Qed.

  Hint Resolve createtmp_right_mover.

  Lemma writetmp_right_mover : forall fn data,
    right_mover
      DeliverAPI.step
      (DeliverAPI.WriteTmp fn data).
  Proof.
    unfold right_mover; intros.
    repeat step_inv.
    - eexists; split.
      + econstructor.
        contradict H12.
        eapply FMap.in_add; eauto.
      + rewrite FMap.add_add_ne by congruence.
        econstructor.
        eapply FMap.in_add; eauto.
    - eexists; split.
      + econstructor.
        eapply FMap.in_add_ne; eauto.
        congruence.
      + rewrite FMap.add_add_ne by congruence.
        econstructor.
        eapply FMap.in_add; eauto.
    - eexists; split; eauto.
      rewrite <- FMap.add_remove_ne by congruence.
      econstructor.
      eapply FMap.in_remove_ne; eauto.
      congruence.
    - eexists; split; eauto.
      econstructor; eauto.
      eapply FMap.mapsto_add_ne; eauto.
      congruence.
    - eauto 20.
    - eauto 20.
    - eauto 20.
    - eauto 20.
  Qed.

  Hint Resolve writetmp_right_mover.

  Lemma unlinktmp_always_enabled : forall fn,
    always_enabled
      DeliverAPI.step
      (DeliverAPI.UnlinkTmp fn).
  Proof.
    unfold always_enabled, enabled_in; intros.
    destruct s; eauto.
  Qed.

  Hint Resolve unlinktmp_always_enabled.

  Lemma unlinktmp_left_mover : forall fn,
    left_mover
      DeliverAPI.step
      (DeliverAPI.UnlinkTmp fn).
  Proof.
    split; eauto.
    intros; repeat step_inv; eauto; repeat deex.
    + eexists; split; eauto.
      rewrite <- FMap.add_remove_ne by congruence.
      econstructor.
      contradict H11.
      eapply FMap.in_remove; eauto.
    + eexists; split; eauto.
      rewrite <- FMap.add_remove_ne by congruence.
      econstructor.
      eapply FMap.in_remove_ne; eauto.
      congruence.
    + eexists; split; eauto.
      rewrite FMap.remove_remove.
      econstructor.
    + eexists; split; eauto.
      econstructor; eauto.
      eapply FMap.mapsto_remove_ne; eauto.
      congruence.
  Qed.

  Hint Resolve unlinktmp_left_mover.

  Theorem deliver_atomic : forall `(rx : _ -> proc _ T) m,
    trace_incl DeliverAPI.step
      (Bind (compile_op (MailboxAPI.Deliver m)) rx)
      (Bind (atomize compile_op (MailboxAPI.Deliver m)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold deliver_core, ysa_movers.
    eauto 20.
  Qed.

  Theorem list_atomic : forall `(rx : _ -> proc _ T),
    trace_incl DeliverAPI.step
      (Bind (compile_op (MailboxAPI.List)) rx)
      (Bind (atomize compile_op (MailboxAPI.List)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold list_core, ysa_movers.
    eauto 20.
  Qed.

  Theorem read_atomic : forall `(rx : _ -> proc _ T) fn,
    trace_incl DeliverAPI.step
      (Bind (compile_op (MailboxAPI.Read fn)) rx)
      (Bind (atomize compile_op (MailboxAPI.Read fn)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold read_core, ysa_movers.
    eauto 20.
  Qed.

  Theorem getrequest_atomic : forall `(rx : _ -> proc _ T),
    trace_incl DeliverAPI.step
      (Bind (compile_op (MailboxAPI.GetRequest)) rx)
      (Bind (atomize compile_op (MailboxAPI.GetRequest)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold getrequest_core, ysa_movers.
    eauto 20.
  Qed.

  Theorem respond_atomic : forall `(rx : _ -> proc _ T) Tr (r : Tr),
    trace_incl DeliverAPI.step
      (Bind (compile_op (MailboxAPI.Respond r)) rx)
      (Bind (atomize compile_op (MailboxAPI.Respond r)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold respond_core, ysa_movers.
    eauto 20.
  Qed.

  Theorem my_compile_correct :
    compile_correct compile_op DeliverAPI.step MailboxTmpAbsAPI.step.
  Proof.
    unfold compile_correct; intros.
    destruct op.

    + repeat atomic_exec_inv.
      repeat step_inv; eauto.
      simpl.
      rewrite FMap.add_add.
      rewrite FMap.remove_add by eauto.
      eapply FMap.mapsto_add in H7; subst.
      econstructor.
      eauto.
    + repeat atomic_exec_inv.
      repeat step_inv; eauto.
    + repeat atomic_exec_inv.
      repeat step_inv; eauto.
    + repeat atomic_exec_inv.
      repeat step_inv; eauto.
    + repeat atomic_exec_inv.
      repeat step_inv; eauto.
  Qed.

  Theorem my_atomize_correct :
    atomize_correct compile_op DeliverAPI.step.
  Proof.
    unfold atomize_correct; intros.
    destruct op.
    + rewrite deliver_atomic.
      eapply trace_incl_bind_a.
      eauto.
    + rewrite list_atomic.
      eapply trace_incl_bind_a.
      eauto.
    + rewrite read_atomic.
      eapply trace_incl_bind_a.
      eauto.
    + rewrite getrequest_atomic.
      eapply trace_incl_bind_a.
      eauto.
    + rewrite respond_atomic.
      eapply trace_incl_bind_a.
      eauto.
  Qed.

  Hint Resolve my_compile_correct.
  Hint Resolve my_atomize_correct.

  Theorem all_traces_match :
    forall ts1 ts2,
      proc_match (Compile.compile_ok compile_op) ts1 ts2 ->
      traces_match_ts DeliverAPI.step MailboxTmpAbsAPI.step ts1 ts2.
  Proof.
    intros.
    eapply Compile.compile_traces_match_ts; eauto.
  Qed.

  Definition absR (s1 : DeliverAPI.State) (s2 : MailboxTmpAbsAPI.State) :=
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
        DeliverAPI.initP
        DeliverAPI.step
        MailboxTmpAbsAPI.step (compile_ts ts2) ts2.
  Proof.
    unfold traces_match_abs; intros.
    rewrite H2 in *; clear H2.
    eapply all_traces_match; eauto.
    eapply Compile.compile_ts_ok; eauto.
  Qed.

  Theorem absInitP :
    forall s1 s2,
      DeliverAPI.initP s1 ->
      absR s1 s2 ->
      MailboxTmpAbsAPI.initP s2.
  Proof.
    eauto.
  Qed.

End AtomicDeliver.
