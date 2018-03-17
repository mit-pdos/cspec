Require Import POCS.
Require Import String.
Require Import DeliverAPI.
Require Import MailboxAPI.
Require Import MailboxTmpAbsAPI.


Module AtomicDeliverRestricted <: LayerImplFollowsRule DeliverRestrictedAPI MailboxTmpAbsAPI DeliverTmpExistenceRule.

  Definition deliver_core (m : string) :=
    _ <- Op (DeliverAPI.CreateWriteTmp m);
    _ <- Op (DeliverAPI.LinkMail);
    _ <- Op (DeliverAPI.UnlinkTmp);
    Ret tt.

  Definition compile_op T (op : MailboxAPI.opT T) : proc _ T :=
    match op with
    | MailboxAPI.Deliver m => deliver_core m
    | MailboxAPI.List => Op (DeliverAPI.List)
    | MailboxAPI.Read fn => Op (DeliverAPI.Read fn)
    | MailboxAPI.Delete fn => Op (DeliverAPI.Delete fn)
    | MailboxAPI.Lock => Op (DeliverAPI.Lock)
    | MailboxAPI.Unlock => Op (DeliverAPI.Unlock)
    | MailboxAPI.Ext extop => Op (DeliverAPI.Ext extop)
    end.

  Ltac step_inv :=
    match goal with
    | H : MailboxAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : MailboxTmpAbsAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : DeliverRestrictedAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : DeliverAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : DeliverRestrictedAPI.step_allow _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    end; intuition idtac.

  Hint Extern 1 (MailboxAPI.step _ _ _ _ _ _) => econstructor.
  Hint Extern 1 (MailboxTmpAbsAPI.step _ _ _ _ _ _) => econstructor.
  Hint Extern 1 (DeliverRestrictedAPI.step _ _ _ _ _ _) => econstructor.
  Hint Extern 1 (DeliverRestrictedAPI.step_allow _ _ _) => econstructor.
  Hint Extern 1 (DeliverAPI.step _ _ _ _ _ _) => econstructor.

  Lemma tid_neq : forall (tid1 tid2 : nat),
    tid1 <> tid2 ->
    (tid1, 0) <> (tid2, 0).
  Proof.
    congruence.
  Qed.

  Hint Resolve tid_neq.
  Hint Resolve FMap.add_incr.
  Hint Resolve FMap.in_add_ne.
  Hint Resolve FMap.in_remove.
  Hint Resolve FMap.in_remove_ne.

  Lemma createwritetmp_right_mover : forall data,
    right_mover
      DeliverRestrictedAPI.step
      (DeliverAPI.CreateWriteTmp data).
  Proof.
    unfold right_mover; intros.
    repeat step_inv.
    - eexists; split; eauto 10.
      rewrite FMap.add_add_ne by congruence.
      eauto 10.
    - eexists; split; eauto.
      rewrite <- FMap.add_remove_ne by congruence.
      eauto 10.
    - eexists; split; eauto.
      econstructor; eauto.
      econstructor; eauto.
      eapply FMap.mapsto_add_ne; eauto.
    - eauto 20.
    - eauto 20.
    - eauto 20.
    - eauto 20.
    - eauto 20.
    - eauto 20.
    - eauto 20.
  Qed.

  Hint Resolve createwritetmp_right_mover.

  Lemma unlinktmp_always_enabled :
    always_enabled
      DeliverRestrictedAPI.step
      (DeliverAPI.UnlinkTmp).
  Proof.
    unfold always_enabled, enabled_in; intros.
    destruct s; eauto.
  Qed.

  Hint Resolve unlinktmp_always_enabled.

  Lemma unlinktmp_left_mover :
    left_mover
      DeliverRestrictedAPI.step
      (DeliverAPI.UnlinkTmp).
  Proof.
    split; eauto.
    intros; repeat step_inv; eauto; repeat deex.
    + eexists; split; eauto.
      rewrite <- FMap.add_remove_ne by congruence.
      eauto 10.
    + eexists; split; eauto.
      rewrite FMap.remove_remove.
      eauto.
    + eexists; split; eauto.
      econstructor; eauto.
      econstructor; eauto.
      eapply FMap.mapsto_remove_ne; eauto.
    + eexists; split; eauto.
    + eexists; split; eauto.
    + eexists; split; eauto.
  Qed.

  Hint Resolve unlinktmp_left_mover.

  Theorem deliver_atomic : forall `(rx : _ -> proc _ T) m,
    trace_incl DeliverRestrictedAPI.step
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
    compile_correct compile_op DeliverRestrictedAPI.step MailboxTmpAbsAPI.step.
  Proof.
    unfold compile_correct; intros.
    destruct op.

    all: repeat atomic_exec_inv; repeat step_inv; eauto.

    simpl.
    eapply FMap.mapsto_add in H10; subst.
    eauto.
  Qed.

  Theorem my_atomize_correct :
    atomize_correct compile_op DeliverRestrictedAPI.step.
  Proof.
    unfold atomize_correct; intros.
    destruct op; try trace_incl_simple.

    rewrite deliver_atomic.
    eapply trace_incl_bind_a.
    eauto.
  Qed.

  Hint Resolve my_compile_correct.
  Hint Resolve my_atomize_correct.

  Theorem all_traces_match :
    forall ts1 ts2,
      proc_match (Compile.compile_ok compile_op) ts1 ts2 ->
      traces_match_ts DeliverRestrictedAPI.step MailboxTmpAbsAPI.step ts1 ts2.
  Proof.
    intros.
    eapply Compile.compile_traces_match_ts; eauto.
  Qed.

  Definition absR (s1 : DeliverRestrictedAPI.State) (s2 : MailboxTmpAbsAPI.State) :=
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
        DeliverRestrictedAPI.initP
        DeliverRestrictedAPI.step
        MailboxTmpAbsAPI.step (compile_ts ts2) ts2.
  Proof.
    unfold traces_match_abs; intros.
    rewrite H2 in *; clear H2.
    eapply all_traces_match; eauto.
    eapply Compile.compile_ts_ok; eauto.
  Qed.

  Theorem absInitP :
    forall s1 s2,
      DeliverRestrictedAPI.initP s1 ->
      absR s1 s2 ->
      MailboxTmpAbsAPI.initP s2.
  Proof.
    eauto.
  Qed.


  Ltac exec_propagate :=
    match goal with
    | s : DeliverAPI.State |- _ =>
      destruct s
    | H : exec_any _ _ _ (Op _) _ _ |- _ =>
      eapply exec_any_op in H; repeat deex
    end.

  Lemma createwritetmp_follows_protocol : forall tid s data,
    follows_protocol_proc
      DeliverAPI.step
      DeliverRestrictedAPI.step_allow
      tid s (deliver_core data).
  Proof.
    destruct s; simpl.
    intros.

    constructor; intros.
      constructor; intros. eauto.

    repeat exec_propagate.
      unfold restricted_step in *; intuition idtac; repeat step_inv.
    constructor; intros.
      constructor; intros. econstructor. eapply FMap.add_in.

    constructor; intros.
      constructor; intros. eauto.
    eauto.
  Qed.

  Hint Resolve createwritetmp_follows_protocol.

  Theorem compile_ts_follows_protocol :
    forall ts,
      no_atomics_ts ts ->
      DeliverTmpExistenceRule.follows_protocol (compile_ts ts).
  Proof.
    unfold compile_ts.
    unfold DeliverTmpExistenceRule.follows_protocol.
    unfold follows_protocol_s.
    intros.
    eapply compile_ts_follows_protocol_proc; try eassumption.
    intros.

    destruct op; simpl; eauto.
  Qed.

End AtomicDeliverRestricted.


Module AtomicDeliverUnrestricted <: LayerImplRequiresRule DeliverAPI DeliverRestrictedAPI DeliverTmpExistenceRule.

  Import DeliverTmpExistenceRule.

  Definition absR (s1 : DeliverAPI.State) (s2 : DeliverRestrictedAPI.State) :=
    s1 = s2.

  Ltac step_inv :=
    match goal with
    | H : DeliverAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : DeliverRestrictedAPI.step_allow _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : DeliverRestrictedAPI.step _ _ _ _ _ _ |- _ =>
      destruct H; intuition idtac
    end.

  Theorem allowed_stable :
    forall `(op : DeliverRestrictedAPI.opT T) `(op' : DeliverRestrictedAPI.opT T') tid tid' s s' r evs,
      tid <> tid' ->
      DeliverRestrictedAPI.step_allow op tid s ->
      DeliverRestrictedAPI.step op' tid' s r s' evs ->
      DeliverRestrictedAPI.step_allow op tid s'.
  Proof.
    intros.
    destruct op; destruct op'; repeat step_inv; subst; eauto.
  Qed.

  Definition compile_ts (ts : @threads_state DeliverRestrictedAPI.opT) := ts.

  Theorem compile_ts_no_atomics :
    forall ts,
      no_atomics_ts ts ->
      no_atomics_ts (compile_ts ts).
  Proof.
    unfold compile_ts; eauto.
  Qed.

  Theorem absInitP :
    forall s1 s2,
      DeliverAPI.initP s1 ->
      absR s1 s2 ->
      DeliverRestrictedAPI.initP s2.
  Proof.
    firstorder.
  Qed.

  Theorem compile_traces_match :
    forall ts,
      follows_protocol ts ->
      no_atomics_ts ts ->
      traces_match_abs absR
        DeliverAPI.initP
        DeliverAPI.step
        DeliverRestrictedAPI.step (compile_ts ts) ts.
  Proof.
    unfold compile_ts, follows_protocol, absR.
    unfold traces_match_abs; intros; subst.
    clear H1.
    specialize (H sm).
    destruct H2.
    induction H1; eauto.
    specialize (H tid _ p) as Htid.
    intuition idtac; repeat deex.

    edestruct IHexec.
      eapply follows_protocol_s_exec_tid_upd; eauto.
      intros; eapply allowed_stable; eauto.
      destruct result; eauto.

    eexists; intuition idtac.
    eapply ExecPrefixOne.
      eauto.
      eapply follows_protocol_preserves_exec_tid'; eauto.
      eauto.
    eauto.
  Qed.

End AtomicDeliverUnrestricted.


Module AtomicDeliver :=
  LinkWithRule DeliverAPI DeliverRestrictedAPI MailboxTmpAbsAPI DeliverTmpExistenceRule
               AtomicDeliverUnrestricted AtomicDeliverRestricted.
