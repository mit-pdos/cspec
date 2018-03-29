Require Import POCS.
Require Import String.
Require Import MailServerAPI.
Require Import MailboxAPI.
Require Import DeliverAPI.
Require Import MailFSAPI.
Require Import MailboxTmpAbsAPI.


Module TryDeliverImpl' <:
  LayerImplMoversT
    MailboxTmpAbsState
    MailFSOp     MailFSAPI
    DeliverOp    DeliverAPI.

  Definition linkmail_core :=
    ts <- Op MailFSOp.Random;
    ok <- Op (MailFSOp.LinkMail ts);
    Ret ok.

  Definition compile_op T (op : DeliverOp.opT T) : proc MailFSOp.opT T :=
    match op with
    | DeliverOp.CreateWriteTmp data => Op (MailFSOp.CreateWriteTmp data)
    | DeliverOp.LinkMail => linkmail_core
    | DeliverOp.UnlinkTmp => Op (MailFSOp.UnlinkTmp)
    | DeliverOp.List => Op (MailFSOp.List)
    | DeliverOp.Read fn => Op (MailFSOp.Read fn)
    | DeliverOp.Delete fn => Op (MailFSOp.Delete fn)
    | DeliverOp.Lock => Op (MailFSOp.Lock)
    | DeliverOp.Unlock => Op (MailFSOp.Unlock)
    | DeliverOp.Ext extop => Op (MailFSOp.Ext extop)
    end.

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
    | H : MailFSAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    end; intuition idtac.

  Hint Extern 1 (DeliverAPI.step _ _ _ _ _ _) => econstructor.
  Hint Extern 1 (MailFSAPI.step _ _ _ _ _ _) => econstructor.

  Lemma random_right_mover :
    right_mover
      MailFSAPI.step
      (MailFSOp.Random).
  Proof.
    unfold right_mover; intros.
    repeat step_inv; eauto 10.

    eexists; split; econstructor.
  Qed.

  Hint Resolve random_right_mover.

  Theorem ysa_movers_linkmail_core :
    ysa_movers MailFSAPI.step linkmail_core.
  Proof.
    econstructor; eauto 20.
  Qed.

  Hint Resolve ysa_movers_linkmail_core.

  Theorem ysa_movers : forall `(op : _ T),
    ysa_movers MailFSAPI.step (compile_op op).
  Proof.
    destruct op; simpl; eauto 20.
  Qed.

  Theorem compile_correct :
    compile_correct compile_op MailFSAPI.step DeliverAPI.step.
  Proof.
    unfold compile_correct; intros.
    destruct op.

    all: repeat atomic_exec_inv; repeat step_inv; eauto.
  Qed.

End TryDeliverImpl'.


Module TryDeliverImpl :=
  LayerImplMovers
    MailboxTmpAbsState
    MailFSOp     MailFSAPI
    DeliverOp    DeliverAPI
    TryDeliverImpl'.

Module TryDeliverImplH' :=
  LayerImplMoversHT
    MailboxTmpAbsState
    MailFSOp     MailFSAPI
    DeliverOp    DeliverAPI
    TryDeliverImpl'
    UserIdx.

Module TryDeliverImplH :=
  LayerImplMovers
    MailboxTmpAbsHState
    MailFSHOp     MailFSHAPI
    DeliverHOp    DeliverHAPI
    TryDeliverImplH'.
