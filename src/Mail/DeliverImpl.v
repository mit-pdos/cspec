Require Import CSPEC.
Require Import MailServerAPI.
Require Import DeliverAPI.
Require Import MailboxAPI.
Require Import MailboxTmpAbsAPI.

Set Printing Projections.
Import Protocol Layer.

Module AtomicDeliver'.

  (* START CODE *)

  Definition deliver_core (m : string) :=
    ok <- Call (DeliverOp.CreateWriteTmp m);
    match ok with
    | true =>
      ok <- Call (DeliverOp.LinkMail);
      _ <- Call (DeliverOp.UnlinkTmp);
      Ret ok
    | false =>
      _ <- Call (DeliverOp.UnlinkTmp);
      Ret false
    end.

  Definition compile_op T (op : MailboxOp.Op T) : proc _ T :=
    match op with
    | MailboxOp.Deliver m => deliver_core m
    | MailboxOp.List => Call (DeliverOp.List)
    | MailboxOp.Read fn => Call (DeliverOp.Read fn)
    | MailboxOp.Delete fn => Call (DeliverOp.Delete fn)
    | MailboxOp.Lock => Call (DeliverOp.Lock)
    | MailboxOp.Unlock => Call (DeliverOp.Unlock)
    | MailboxOp.Ext extop => Call (DeliverOp.Ext extop)
    end.

  (* END CODE *)

  Theorem compile_op_no_atomics :
    forall `(op : _ T),
      no_atomics (compile_op op).
  Proof.
    destruct op; compute; eauto.
    econstructor; eauto.
    destruct x; eauto.
  Qed.

  Ltac step_inv :=
    (* TODO: add other things to unfold here (or just unfold all the
    layer/protocol .l's and .p's) *)
    cbn [Layer.step DeliverAPI.l] in *;
    match goal with
    | H : MailboxAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : MailboxTmpAbsAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : DeliverRestrictedAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : DeliverAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : DeliverProtocol.step_allow _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    end; intuition idtac.

  Hint Extern 1 (MailboxAPI.step _ _ _ _ _ _) => econstructor.
  Hint Extern 1 (MailboxTmpAbsAPI.step _ _ _ _ _ _) => econstructor.
  Hint Extern 1 (DeliverRestrictedAPI.step _ _ _ _ _ _) => econstructor.
  Hint Extern 1 (DeliverProtocol.step_allow _ _ _) => econstructor.
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
      DeliverRestrictedAPI.l.(Layer.step)
      (DeliverOp.CreateWriteTmp data).
  Proof.
    unfold right_mover; intros.
    repeat step_inv; eauto 10.
    - eexists; split; eauto 10.
      rewrite FMap.add_add_ne by congruence.
      eauto 10.
    - eexists; split; eauto 10.
      rewrite FMap.add_add_ne by congruence.
      eauto 10.
    - eexists.
      rewrite FMap.add_add_ne by congruence.
      split.
      2: eauto.
      eauto.
    - eexists; split.
      2: eauto 10.
      eauto.
    - eexists.
      rewrite FMap.add_add_ne by congruence.
      split; ( constructor; [ eauto | ] ).
      eapply DeliverAPI.StepCreateWriteTmpErr2.
      eapply DeliverAPI.StepCreateWriteTmpErr2.
    - eexists; split; eauto 10.
      rewrite <- FMap.add_remove_ne by congruence.
      eauto 10.
    - eexists; split; eauto 10.
      rewrite <- FMap.add_remove_ne by congruence.
      eauto 10.
    - eexists; split; eauto.
      econstructor; eauto.
      econstructor; eauto.
      eapply FMap.mapsto_add_ne; eauto.
    - eapply FMap.mapsto_add_ne in H13; try congruence.
      eexists; split.
      eauto 8.
      eauto.
  Qed.

  Hint Resolve createwritetmp_right_mover.

  Lemma unlinktmp_always_enabled :
    always_enabled
      DeliverRestrictedAPI.l.(Layer.step)
      (DeliverOp.UnlinkTmp).
  Proof.
    unfold always_enabled, enabled_in; unfold Layer.step; unfold DeliverRestrictedAPI.l; intros.
    destruct s; eauto.
  Qed.

  Hint Resolve unlinktmp_always_enabled.

  Lemma unlinktmp_left_mover :
    left_mover
      DeliverRestrictedAPI.l.(Layer.step)
      (DeliverOp.UnlinkTmp).
  Proof.
    split; eauto.
    unfold Layer.step; unfold DeliverRestrictedAPI.l; intros.
    repeat step_inv; eauto; repeat deex.
    + eexists; split; eauto.
      rewrite <- FMap.add_remove_ne by congruence.
      eauto 10.
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
    + eexists; split; eauto.
  Qed.

  Hint Resolve unlinktmp_left_mover.

  Theorem ysa_movers : forall `(op : _ T),
    ysa_movers DeliverRestrictedAPI.l.(Layer.step) (compile_op op).
  Proof.
    unfold Layer.step; unfold DeliverRestrictedAPI.l.
    destruct op; simpl; eauto 20.
    econstructor; eauto.
    destruct r; eauto.
  Qed.

  Theorem compile_correct :
    compile_correct compile_op DeliverRestrictedAPI.l.(Layer.step) MailboxTmpAbsAPI.l.(Layer.step).
  Proof.
    unfold compile_correct; unfold Layer.step; unfold MailboxTmpAbsAPI.l; unfold DeliverRestrictedAPI.l; intros.
    destruct op.

    + atomic_exec_inv.
      destruct v1.
      - repeat atomic_exec_inv; repeat step_inv; eauto; simpl; try congruence.
        eapply FMap.mapsto_add in H10; subst; eauto.
      - repeat atomic_exec_inv; repeat step_inv; eauto; simpl; try congruence.
    + atomic_exec_inv; repeat step_inv; eauto.
    + atomic_exec_inv; repeat step_inv; eauto.
    + atomic_exec_inv; repeat step_inv; eauto.
    + atomic_exec_inv; repeat step_inv; eauto.
    + atomic_exec_inv; repeat step_inv; eauto.
    + atomic_exec_inv; repeat step_inv; eauto.
  Qed.


  Ltac exec_propagate :=
    match goal with
    | s : MailboxTmpAbsState.State |- _ =>
      destruct s
    | H : exec_any _ _ _ (Call _) _ _ |- _ =>
      eapply exec_any_op in H; repeat deex
    end.

  Lemma deliver_follows_protocol : forall tid s data,
    follows_protocol_proc
      DeliverAPI.l.(Layer.step)
      DeliverProtocol.p.(Protocol.step_allow)
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

    constructor; intros.
      constructor; intros. eauto.
      constructor; intros. eauto.
  Qed.

  Hint Resolve deliver_follows_protocol.

  Theorem op_follows_protocol :
    forall tid S T (op : _ T),
      follows_protocol_proc
        DeliverAPI.l.(Layer.step)
        DeliverProtocol.p.(Protocol.step_allow)
        tid S (compile_op op).
  Proof.
    destruct op; simpl; eauto.
  Qed.

  Theorem allowed_stable :
    forall `(op : DeliverOp.Op T) `(op' : DeliverOp.Op T') tid tid' S S' r evs,
      tid <> tid' ->
      DeliverProtocol.p.(Protocol.step_allow) T op tid S ->
      DeliverRestrictedAPI.l.(Layer.step) op' tid' S r S' evs ->
      DeliverProtocol.p.(Protocol.step_allow) T op tid S'.
  Proof.
    unfold Layer.step; unfold Protocol.step_allow; unfold DeliverProtocol.p.
    unfold DeliverRestrictedAPI.l; intros.
    destruct op; destruct op'; repeat step_inv; subst; eauto.
  Qed.

  Theorem raw_step_ok :
    forall `(op : _ T) tid s r s' evs,
      restricted_step DeliverAPI.l.(Layer.step) DeliverProtocol.p.(Protocol.step_allow) op tid s r s' evs ->
      DeliverRestrictedAPI.l.(Layer.step) op tid s r s' evs.
  Proof.
    eauto.
  Qed.

  Definition initP_compat : forall s, DeliverRestrictedAPI.l.(Layer.initP) s ->
                                 MailboxTmpAbsAPI.l.(Layer.initP) s :=
    ltac:(auto).

  Definition raw_initP_compat : forall s, DeliverAPI.l.(Layer.initP) s ->
                                     DeliverRestrictedAPI.l.(Layer.initP) s :=
    ltac:(auto).

  Definition movers_impl : LayerImplMoversT.t DeliverRestrictedAPI.l MailboxTmpAbsAPI.l.
    refine {| LayerImplMoversT.compile_op := compile_op;
       LayerImplMoversT.compile_op_no_atomics := @compile_op_no_atomics;
       LayerImplMoversT.ysa_movers := @ysa_movers;
       LayerImplMoversT.compile_correct := @compile_correct;
       LayerImplMoversT.initP_compat := @initP_compat; |}.
    Defined.
  
  Definition t : LayerImplMoversProtocolT.t
                   DeliverAPI.l DeliverRestrictedAPI.l MailboxTmpAbsAPI.l
                   DeliverProtocol.p.
    refine {| LayerImplMoversProtocolT.movers_impl := @movers_impl;
              LayerImplMoversProtocolT.raw_step_ok := @raw_step_ok;
              LayerImplMoversProtocolT.allowed_stable := @allowed_stable;
              LayerImplMoversProtocolT.raw_initP_compat := @raw_initP_compat;
              LayerImplMoversProtocolT.op_follows_protocol := @op_follows_protocol;|}.
    Defined.
    
End AtomicDeliver'.

Definition AtomicDeliver :=
  LayerImplMoversProtocol.t AtomicDeliver'.t.

Definition AtomicDeliverH' :=
  LayerImplMoversProtocolHT.t
    AtomicDeliver'.t
    UserIdx.idx.

Module AtomicDeliverH :=
  LayerImplMoversProtocol
    MailboxTmpAbsHState
    DeliverHOp DeliverHAPI DeliverRestrictedHAPI
    MailboxHOp MailboxTmpAbsHAPI
    DeliverHProtocol
    AtomicDeliverH'.
