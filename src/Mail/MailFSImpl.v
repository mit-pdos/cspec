Require Import CSPEC.
Require Import MailServerAPI.
Require Import MailboxTmpAbsAPI.
Require Import DeliverListTidAPI.
Require Import MailFSAPI.


Module MailFSImpl' <:
  LayerImplMoversT
    MailboxTmpAbsState
    MailFSOp  MailFSAPI
    DeliverListTidOp DeliverListTidAPI.

  (* START CODE *)

  Definition same_tid (tid : nat) (fn : nat * nat) : bool :=
    if tid == fst fn then
      true
    else
      false.

  Definition listtid_core :=
    tid <- Call (MailFSOp.GetTID);
    l <- Call (MailFSOp.List);
    Ret (map snd (filter (same_tid tid) l)).

  Definition createwrite_core data :=
    ok1 <- Call (MailFSOp.CreateTmp);
    if (ok1 : bool) then Call (MailFSOp.WriteTmp data) else Ret ok1.

  Definition compile_op T (op : DeliverListTidOp.Op T) : proc _ T :=
    match op with
    | DeliverListTidOp.LinkMail m => Call (MailFSOp.LinkMail m)
    | DeliverListTidOp.List => Call (MailFSOp.List)
    | DeliverListTidOp.ListTid => listtid_core
    | DeliverListTidOp.Read fn => Call (MailFSOp.Read fn)
    | DeliverListTidOp.Delete fn => Call (MailFSOp.Delete fn)
    | DeliverListTidOp.CreateWriteTmp data => createwrite_core data
    | DeliverListTidOp.UnlinkTmp => Call (MailFSOp.UnlinkTmp)
    | DeliverListTidOp.Lock => Call (MailFSOp.Lock)
    | DeliverListTidOp.Unlock => Call (MailFSOp.Unlock)
    | DeliverListTidOp.Ext extop => Call (MailFSOp.Ext extop)
    end.

  (* END CODE *)

  Theorem compile_op_no_atomics :
    forall `(op : _ T),
      no_atomics (compile_op op).
  Proof.
    destruct op; compute; eauto.

    constructor; eauto.
    destruct x; eauto.
  Qed.

  Ltac step_inv :=
    match goal with
    | H : MailFSAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : MailFSAPI.xstep _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : DeliverListTidAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    end; intuition idtac.

  Hint Extern 1 (MailFSAPI.step _ _ _ _ _ _) => econstructor.
  Hint Extern 1 (DeliverListTidAPI.step _ _ _ _ _ _) => econstructor.
  Hint Constructors MailFSAPI.xstep.

  Lemma gettid_right_mover :
    right_mover
      MailFSAPI.step
      (MailFSOp.GetTID).
  Proof.
    unfold right_mover; intros.
    repeat step_inv; eauto 10.

    eexists; split; econstructor; eauto.
  Qed.

  Hint Resolve gettid_right_mover.

  Lemma fmap_in_tid_ne :
    forall (tid0 tid1 : nat) (x y : nat) TV (v : TV) m,
      tid0 <> tid1 ->
      FMap.In (tid0, x) (FMap.add (tid1, y) v m) ->
      FMap.In (tid0, x) m.
  Proof.
    intros.
    eapply FMap.in_add_ne; eauto.
    congruence.
  Qed.

  Hint Resolve fmap_in_tid_ne.

  Lemma createtmp_right_mover :
    right_mover
      MailFSAPI.step
      (MailFSOp.CreateTmp).
  Proof.
    unfold right_mover; intros.
    repeat step_inv; eauto 10.

    all: unfold MailFSAPI.step.
    all: try solve [ rewrite FMap.add_add_ne by congruence; eauto 10 ].

    rewrite FMap.add_add_ne by congruence.
      eexists. split. 2: eauto. eauto.

    rewrite <- FMap.add_remove_ne by congruence.
      eexists. split. 2: eauto. eauto.

    eapply FMap.mapsto_add_ne in H12; try congruence.
      eexists. split. 2: eauto. eauto.

    eexists. split. 2: eauto. eauto.
  Qed.

  Hint Resolve createtmp_right_mover.

  Theorem ysa_movers_listtid_core:
    ysa_movers MailFSAPI.step listtid_core.
  Proof.
    econstructor; eauto 20.
  Qed.

  Hint Resolve ysa_movers_listtid_core.

  Theorem ysa_movers_createwrite_core:
    forall data,
      ysa_movers MailFSAPI.step (createwrite_core data).
  Proof.
    econstructor; eauto 20.
    destruct r; eauto 20.
  Qed.

  Hint Resolve ysa_movers_createwrite_core.

  Theorem ysa_movers : forall `(op : _ T),
    ysa_movers MailFSAPI.step (compile_op op).
  Proof.
    destruct op; simpl; eauto 20.
  Qed.

  Theorem compile_correct :
    compile_correct compile_op MailFSAPI.step DeliverListTidAPI.step.
  Proof.
    unfold compile_correct; intros.
    destruct op.

    all: try solve [ repeat atomic_exec_inv; repeat step_inv; eauto ].

    - repeat atomic_exec_inv; repeat step_inv; eauto.
      rewrite FMap.add_add; eauto.
      rewrite FMap.add_add; eauto.

    - repeat atomic_exec_inv.
      repeat step_inv; eauto.
      econstructor; intros.

      eapply in_map_iff.
      exists (v1, fn); intuition eauto.
      eapply filter_In; intuition eauto.
      eapply FMap.is_permutation_in'; eauto.
      unfold same_tid; simpl.
      destruct (v1 == v1); congruence.
  Qed.

  Definition initP_compat : forall s, MailFSAPI.initP s ->
                                 DeliverListTidAPI.initP s :=
    ltac:(auto).

End MailFSImpl'.

Module MailFSImpl :=
  LayerImplMovers
    MailboxTmpAbsState
    MailFSOp MailFSAPI
    DeliverListTidOp DeliverListTidAPI
    MailFSImpl'.

Module MailFSImplH' :=
  LayerImplMoversHT
    MailboxTmpAbsState
    MailFSOp MailFSAPI
    DeliverListTidOp DeliverListTidAPI
    MailFSImpl'
    UserIdx.

Module MailFSImplH :=
  LayerImplMovers
    MailboxTmpAbsHState
    MailFSHOp MailFSHAPI
    DeliverListTidHOp DeliverListTidHAPI
    MailFSImplH'.
