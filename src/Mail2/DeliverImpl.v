Require Import POCS.
Require Import String.
Require Import DeliverAPI.


Module AtomicDeliver <: LayerImpl TmpdirAPI MailboxAPI.

  Definition deliver_core (m : string) :=
    tmpfn <- Op (TmpdirAPI.CreateTmp m);
    _ <- Op (TmpdirAPI.LinkMail tmpfn);
    _ <- Op (TmpdirAPI.UnlinkTmp tmpfn);
    Ret tt.

  Definition compile_op T (op : MailboxAPI.opT T) : proc _ T :=
    match op with
    | MailboxAPI.Deliver m => deliver_core m
    end.

  Ltac step_inv :=
    match goal with
    | H : MailboxAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : TmpdirAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    end; intuition idtac.

  Hint Extern 1 (MailboxAPI.step _ _ _ _ _ _) => econstructor.
  Hint Extern 1 (TmpdirAPI.step _ _ _ _ _ _) => econstructor.

  Lemma createtmp_right_mover : forall m,
    right_mover
      TmpdirAPI.step
      (TmpdirAPI.CreateTmp m).
  Proof.
    unfold right_mover; intros.
    repeat step_inv.
    - eexists; split.
      + econstructor.
        contradict H12.
        eapply FMap.in_add; eauto.
      + rewrite FMap.add_add_ne by congruence.
        econstructor.
        contradict H2.
        eapply FMap.in_add_ne; eauto.
        congruence.
    - eexists; split; eauto.
      rewrite <- FMap.add_remove_ne by congruence.
      econstructor.
      contradict H2.
      eapply FMap.in_remove; eauto.
    - eexists; split; eauto.
      econstructor; eauto.
      eapply FMap.mapsto_add_ne; eauto.
      congruence.
  Qed.

  Hint Resolve createtmp_right_mover.

  Lemma unlinktmp_always_enabled : forall fn,
    always_enabled
      TmpdirAPI.step
      (TmpdirAPI.UnlinkTmp fn).
  Proof.
    unfold always_enabled, enabled_in; intros.
    destruct s; eauto.
  Qed.

  Hint Resolve unlinktmp_always_enabled.

  Lemma unlinktmp_left_mover : forall fn,
    left_mover
      TmpdirAPI.step
      (TmpdirAPI.UnlinkTmp fn).
  Proof.
    split; eauto.
    intros; repeat step_inv; eauto; repeat deex.
    + eexists; split; eauto.
      rewrite <- FMap.add_remove_ne by congruence.
      econstructor.
      contradict H11.
      eapply FMap.in_remove; eauto.
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
    trace_incl TmpdirAPI.step
      (Bind (compile_op (MailboxAPI.Deliver m)) rx)
      (Bind (atomize compile_op (MailboxAPI.Deliver m)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold deliver_core, ysa_movers.
    eauto 20.
  Qed.

  Theorem my_compile_correct :
    compile_correct compile_op TmpdirAPI.step MailboxAPI.step.
  Proof.
    unfold compile_correct; intros.
    destruct op.

    + repeat atomic_exec_inv.
      repeat step_inv; eauto.
      simpl.
      rewrite FMap.remove_add.
      eapply FMap.mapsto_add in H7; subst.
      econstructor.
      eauto.
  Qed.

  Theorem my_atomize_correct :
    atomize_correct compile_op TmpdirAPI.step.
  Proof.
    unfold atomize_correct; intros.
    destruct op.
    + rewrite deliver_atomic.
      eapply trace_incl_bind_a.
      eauto.
  Qed.

  Hint Resolve my_compile_correct.
  Hint Resolve my_atomize_correct.

  Theorem all_traces_match :
    forall ts1 ts2,
      proc_match (Compile.compile_ok compile_op) ts1 ts2 ->
      traces_match_ts TmpdirAPI.step MailboxAPI.step ts1 ts2.
  Proof.
    intros.
    eapply Compile.compile_traces_match_ts; eauto.
  Qed.

  Definition absR (s1 : TmpdirAPI.State) (s2 : MailboxAPI.State) :=
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
      traces_match_abs absR TmpdirAPI.initP TmpdirAPI.step MailboxAPI.step (compile_ts ts2) ts2.
  Proof.
    unfold traces_match_abs; intros.
    rewrite H2 in *; clear H2.
    eapply all_traces_match; eauto.
    eapply Compile.compile_ts_ok; eauto.
  Qed.

  Theorem absInitP :
    forall s1 s2,
      TmpdirAPI.initP s1 ->
      absR s1 s2 ->
      MailboxAPI.initP s2.
  Proof.
    eauto.
  Qed.

End AtomicDeliver.
