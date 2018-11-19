Require Import CSPEC.
Require Import MailServerAPI.
Require Import MailboxTmpAbsAPI.
Require Import DeliverAPI.
Require Import DeliverListTidAPI.


Module DeliverListTidImpl'.
  Import Layer.
  Import Protocol.

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
    unfold DeliverAPI.l in *;
    unfold DeliverRestrictedAPI.l in *;
    unfold DeliverListTidAPI.l in *;
    unfold DeliverListTidRestrictedAPI.l in *;
    unfold DeliverListTidProtocol.p in *;
    unfold step_allow in *;
    unfold step in *;
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
      DeliverListTidRestrictedAPI.l.(step)
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
    ysa_movers DeliverListTidRestrictedAPI.l.(step) (compile_op op).
  Proof.
    destruct op; simpl; eauto 20.
    unfold linkmail_core; eauto.
  Qed.

  Theorem compile_correct :
    compile_correct compile_op DeliverListTidRestrictedAPI.l.(step) DeliverAPI.l.(step).
  Proof.
    unfold compile_correct; intros.
    destruct op.

    all: repeat atomic_exec_inv; repeat step_inv; eauto.
  Qed.


  Lemma linkmail_follows_protocol : forall tid s,
    follows_protocol_proc
      DeliverListTidAPI.l.(step)
      DeliverListTidProtocol.p.(step_allow)
      tid s (linkmail_core).
  Proof.
    intros.
    constructor; intros.
    unfold step, DeliverListTidAPI.l, step_allow, DeliverListTidProtocol.p.
      constructor; intros. eauto.

    constructor; intros.
      constructor; intros; eauto.

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
        DeliverListTidAPI.l.(step)
        DeliverListTidProtocol.p.(step_allow)
        tid s (compile_op op).
  Proof.
    destruct op; simpl; eauto.
  Qed.

  Theorem allowed_stable :
    forall T (op : DeliverListTidOp.Op T) T' (op' : DeliverListTidOp.Op T') tid tid' s s' r evs,
      tid <> tid' ->
      DeliverListTidProtocol.p.(step_allow) T op tid s ->
      DeliverListTidRestrictedAPI.l.(step) op' tid' s r s' evs ->
      DeliverListTidProtocol.p.(step_allow) T op tid s'.
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
      restricted_step DeliverListTidAPI.l.(step) DeliverListTidProtocol.p.(step_allow) op tid s r s' evs ->
      DeliverListTidRestrictedAPI.l.(step) op tid s r s' evs.
  Proof.
    eauto.
  Qed.

  Definition initP_compat : forall s, DeliverListTidRestrictedAPI.l.(initP) s ->
                                 DeliverAPI.l.(initP) s :=
    ltac:(auto).

  Definition raw_initP_compat : forall s, DeliverListTidRestrictedAPI.l.(initP) s ->
                                     DeliverListTidAPI.l.(initP) s :=
    ltac:(auto).


  Definition movers_impl : LayerImplMoversT.t DeliverListTidRestrictedAPI.l DeliverAPI.l.
    refine {| LayerImplMoversT.compile_op := compile_op;
              LayerImplMoversT.compile_op_no_atomics := @compile_op_no_atomics;
              LayerImplMoversT.ysa_movers := @ysa_movers;
              LayerImplMoversT.compile_correct := @compile_correct;
              LayerImplMoversT.initP_compat := @initP_compat; |}.
  Defined.
  
  Print LayerImplMoversProtocolT.t.
  Definition l : LayerImplMoversProtocolT.t
                 DeliverListTidAPI.l DeliverListTidRestrictedAPI.l DeliverAPI.l
                 DeliverListTidProtocol.p.
    refine {| LayerImplMoversProtocolT.movers_impl := movers_impl;
              LayerImplMoversProtocolT.op_follows_protocol := op_follows_protocol;
              LayerImplMoversProtocolT.allowed_stable := allowed_stable;
              LayerImplMoversProtocolT.raw_step_ok := @raw_step_ok;
              LayerImplMoversProtocolT.raw_initP_compat := raw_initP_compat; |}.
  Defined.
              
End DeliverListTidImpl'.

Definition DeliverListTidImpl := LayerImplMoversProtocol.t DeliverListTidImpl'.l.

Definition DeliverListTidImplH' := LayerImplMoversProtocolHT.t DeliverListTidImpl'.l UserIdx.idx.

Definition DeliverListTidImplH := LayerImplMoversProtocol.t DeliverListTidImplH'.
