Require Import CSPEC.
Require Import MailServerAPI.
Require Import MailboxTmpAbsAPI.
Require Import DeliverAPI.
Require Import DeliverListTidAPI.


Module DeliverListTidImpl' <:
  LayerImplMoversProtocolT
    MailboxTmpAbsState
    DeliverListTidOp DeliverListTidAPI DeliverListTidRestrictedAPI
    DeliverOp        DeliverAPI
    DeliverListTidProtocol.

  (* START CODE *)

  Fixpoint nextfn (files : list nat) (r : nat) : nat :=
    match files with
    | nil => r
    | fn' :: files' =>
      let r' :=
        if (le_dec r fn') then
          fn' + 1
        else
          r
        in
      nextfn files' r'
    end.

  Definition linkmail_core :=
    files <- Call DeliverListTidOp.ListTid;
    let newname := nextfn files 0 in
    ok <- Call (DeliverListTidOp.LinkMail newname);
    Ret ok.

  Definition compile_op T (op : DeliverOp.Op T) : proc _ T :=
    match op with
    | DeliverOp.CreateWriteTmp data => Call (DeliverListTidOp.CreateWriteTmp data)
    | DeliverOp.LinkMail => linkmail_core
    | DeliverOp.UnlinkTmp => Call (DeliverListTidOp.UnlinkTmp)
    | DeliverOp.List => Call (DeliverListTidOp.List)
    | DeliverOp.Read fn => Call (DeliverListTidOp.Read fn)
    | DeliverOp.Delete fn => Call (DeliverListTidOp.Delete fn)
    | DeliverOp.Lock => Call (DeliverListTidOp.Lock)
    | DeliverOp.Unlock => Call (DeliverListTidOp.Unlock)
    | DeliverOp.Ext extop => Call (DeliverListTidOp.Ext extop)
    end.

  (* END CODE *)

  Lemma nextfn_ok' : forall (tid : nat) `(s : FMap.t _ V) r1 r0 n,
    ( forall fn, FMap.In (tid, fn) s -> In fn (r0 ++ r1) ) ->
    ( forall fn, In fn r0 -> n > fn ) ->
    ~ FMap.In (tid, nextfn r1 n) s.
  Proof.
    induction r1; simpl; intros.
    - intro.
      specialize (H _ H1). rewrite app_nil_r in *.
      specialize (H0 _ H).
      omega.
    - eapply IHr1 with (r0 := r0 ++ (a :: nil)); clear IHr1; intros.
      + rewrite <- app_assoc; simpl. eauto.
      + eapply in_app_or in H1; intuition eauto.
        * specialize (H0 _ H2).
          destruct (le_dec n a); simpl; omega.
        * inversion H2; subst. 2: inversion H1.
          destruct (le_dec n fn); simpl; omega.
  Qed.

  Lemma nextfn_ok : forall (tid : nat) `(s : FMap.t _ V) r n,
    ( forall fn, FMap.In (tid, fn) s -> In fn r ) ->
    ~ FMap.In (tid, nextfn r n) s.
  Proof.
    intros.
    eapply nextfn_ok' with (r0 := nil); simpl; intros.
    eapply H; eauto.
    omega.
  Qed.

  Theorem compile_op_no_atomics :
    forall `(op : _ T),
      no_atomics (compile_op op).
  Proof.
    destruct op; compute; eauto.
  Qed.

  Ltac step_inv :=
    match goal with
    | H : DeliverAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : DeliverListTidAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : DeliverListTidProtocol.step_allow _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : DeliverListTidRestrictedAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    end; intuition idtac.

  Hint Extern 1 (DeliverAPI.step _ _ _ _ _ _) => econstructor.
  Hint Extern 1 (DeliverListTidAPI.step _ _ _ _ _ _) => econstructor.
  Hint Extern 1 (DeliverListTidProtocol.step_allow _ _ _) => econstructor.
  Hint Extern 1 (DeliverListTidRestrictedAPI.step _ _ _ _ _ _) => econstructor.

  Lemma listtid_right_mover :
    right_mover
      DeliverListTidRestrictedAPI.step
      (DeliverListTidOp.ListTid).
  Proof.
    unfold right_mover; intros.
    repeat step_inv; eauto 10.
    + eexists; split.
      econstructor. eauto.
        eapply DeliverListTidAPI.StepCreateWriteTmpErr2.
      econstructor; eauto.
    + eexists; split.
      econstructor; eauto.
      econstructor; intros; eauto.
      econstructor; intros; eauto.
      eapply H4.
      eapply FMap.in_add_ne; eauto.
      congruence.
    + eexists; split.
      econstructor; eauto.
      econstructor; intros; eauto.
      econstructor; intros; eauto.
      eapply H4.
      eapply FMap.in_remove; eauto.
  Qed.

  Hint Resolve listtid_right_mover.

  Theorem ysa_movers : forall `(op : _ T),
    ysa_movers DeliverListTidRestrictedAPI.step (compile_op op).
  Proof.
    destruct op; simpl; eauto 20.
    unfold linkmail_core; eauto.
  Qed.

  Theorem compile_correct :
    compile_correct compile_op DeliverListTidRestrictedAPI.step DeliverAPI.step.
  Proof.
    unfold compile_correct; intros.
    destruct op.

    all: repeat atomic_exec_inv; repeat step_inv; eauto.
  Qed.


  Lemma linkmail_follows_protocol : forall tid s,
    follows_protocol_proc
      DeliverListTidAPI.step
      DeliverListTidProtocol.step_allow
      tid s (linkmail_core).
  Proof.
    intros.
    constructor; intros.
      constructor; intros. eauto.

    constructor; intros.
      constructor; intros.

    {
      eapply exec_any_op in H; repeat deex.
      destruct H0.
      repeat step_inv.

      econstructor.
      eapply nextfn_ok; eauto.
    }

    constructor; intros.
  Qed.

  Hint Resolve linkmail_follows_protocol.

  Theorem op_follows_protocol :
    forall tid s `(op : _ T),
      follows_protocol_proc
        DeliverListTidAPI.step
        DeliverListTidProtocol.step_allow
        tid s (compile_op op).
  Proof.
    destruct op; simpl; eauto.
  Qed.

  Theorem allowed_stable :
    forall `(op : DeliverListTidOp.Op T) `(op' : DeliverListTidOp.Op T') tid tid' s s' r evs,
      tid <> tid' ->
      DeliverListTidProtocol.step_allow op tid s ->
      DeliverListTidRestrictedAPI.step op' tid' s r s' evs ->
      DeliverListTidProtocol.step_allow op tid s'.
  Proof.
    intros.
    destruct op; destruct op'; repeat step_inv; subst; eauto.
    - constructor.
      contradict H3.
      eapply FMap.in_add_ne; eauto.
      congruence.
    - constructor.
      contradict H3.
      eapply FMap.in_remove; eauto.
  Qed.

  Theorem raw_step_ok :
    forall `(op : _ T) tid s r s' evs,
      restricted_step DeliverListTidAPI.step DeliverListTidProtocol.step_allow op tid s r s' evs ->
      DeliverListTidRestrictedAPI.step op tid s r s' evs.
  Proof.
    eauto.
  Qed.

  Definition initP_compat : forall s, DeliverListTidRestrictedAPI.initP s ->
                                 DeliverAPI.initP s :=
    ltac:(auto).

  Definition raw_initP_compat : forall s, DeliverListTidRestrictedAPI.initP s ->
                                     DeliverListTidAPI.initP s :=
    ltac:(auto).

End DeliverListTidImpl'.


Module DeliverListTidImpl :=
  LayerImplMoversProtocol
    MailboxTmpAbsState
    DeliverListTidOp DeliverListTidAPI DeliverListTidRestrictedAPI
    DeliverOp        DeliverAPI
    DeliverListTidProtocol
    DeliverListTidImpl'.

Module DeliverListTidImplH' :=
  LayerImplMoversProtocolHT
    MailboxTmpAbsState
    DeliverListTidOp DeliverListTidAPI DeliverListTidRestrictedAPI
    DeliverOp        DeliverAPI
    DeliverListTidProtocol
    DeliverListTidImpl'
    UserIdx.

Module DeliverListTidImplH :=
  LayerImplMoversProtocol
    MailboxTmpAbsHState
    DeliverListTidHOp DeliverListTidHAPI DeliverListTidRestrictedHAPI
    DeliverHOp        DeliverHAPI
    DeliverListTidHProtocol
    DeliverListTidImplH'.
