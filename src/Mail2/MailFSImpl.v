Require Import POCS.
Require Import String.
Require Import MailServerAPI.
Require Import MailboxTmpAbsAPI.
Require Import DeliverListTidAPI.
Require Import MailFSAPI.


Module MailFSImpl' <:
  LayerImplMoversT
    MailboxTmpAbsState
    MailFSOp  MailFSAPI
    DeliverListTidOp DeliverListTidAPI.

  Definition same_tid (tid : nat) (fn : nat * nat) : bool :=
    if tid == fst fn then
      true
    else
      false.

  Definition listtid_core :=
    tid <- Op (MailFSOp.GetTID);
    l <- Op (MailFSOp.List);
    Ret (map snd (filter (same_tid tid) l)).

  Definition compile_op T (op : DeliverListTidOp.opT T) : proc _ T :=
    match op with
    | DeliverListTidOp.LinkMail m => Op (MailFSOp.LinkMail m)
    | DeliverListTidOp.List => Op (MailFSOp.List)
    | DeliverListTidOp.ListTid => listtid_core
    | DeliverListTidOp.Read fn => Op (MailFSOp.Read fn)
    | DeliverListTidOp.Delete fn => Op (MailFSOp.Delete fn)
    | DeliverListTidOp.CreateWriteTmp data => Op (MailFSOp.CreateWriteTmp data)
    | DeliverListTidOp.UnlinkTmp => Op (MailFSOp.UnlinkTmp)
    | DeliverListTidOp.Lock => Op (MailFSOp.Lock)
    | DeliverListTidOp.Unlock => Op (MailFSOp.Unlock)
    | DeliverListTidOp.Ext extop => Op (MailFSOp.Ext extop)
    end.

  Theorem compile_op_no_atomics :
    forall `(op : _ T),
      no_atomics (compile_op op).
  Proof.
    destruct op; compute; eauto.
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

  Lemma gettid_right_mover :
    right_mover
      MailFSAPI.step
      (MailFSOp.GetTID).
  Proof.
    unfold right_mover; intros.
    repeat step_inv; eauto 10.

    eexists; split; econstructor.
  Qed.

  Hint Resolve gettid_right_mover.

  Theorem ysa_movers_listtid_core:
    ysa_movers MailFSAPI.step listtid_core.
  Proof.
    econstructor; eauto 20.
  Qed.

  Hint Resolve ysa_movers_listtid_core.

  Theorem ysa_movers : forall `(op : _ T),
    ysa_movers MailFSAPI.step (compile_op op).
  Proof.
    destruct op; simpl; eauto 20.
    all: admit.
  Admitted.

  Theorem compile_correct :
    compile_correct compile_op MailFSAPI.step DeliverListTidAPI.step.
  Proof.
    unfold compile_correct; intros.
    destruct op.

    all: try solve [ repeat atomic_exec_inv; repeat step_inv; eauto ].

    repeat atomic_exec_inv.
    repeat step_inv; eauto.
    econstructor; intros.

    eapply in_map_iff.
    exists (v1, fn); intuition eauto.
    eapply filter_In; intuition eauto.
    eapply FMap.is_permutation_in'; eauto.
    unfold same_tid; simpl.
    destruct (v1 == v1); congruence.
  Qed.


End MailFSImpl'.

Module MailFSImpl :=
  LayerImplMovers
    MailboxTmpAbsState
    MailFSOp  MailFSAPI
    DeliverListTidOp DeliverListTidAPI.
