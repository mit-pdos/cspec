Require Import CSPEC.
Require Import MailServerAPI.
Require Import MailboxAPI.
Require Import TryDeliverAPI.
Require Import MailFSAPI.
Require Import MailboxTmpAbsAPI.


Module TryDeliverImpl' <:
  LayerImplMoversT
    MailboxTmpAbsState
    MailFSOp     MailFSAPI
    TryDeliverOp TryDeliverAPI.

  (* START CODE *)

  Definition linkmail_core :=
    ts <- Call MailFSOp.Random;
    ok <- Call (MailFSOp.LinkMail ts);
    Ret ok.

  Definition compile_op T (op : TryDeliverOp.Op T) : proc MailFSOp.Op T :=
    match op with
    | TryDeliverOp.CreateWriteTmp data => Call (MailFSOp.CreateWriteTmp data)
    | TryDeliverOp.LinkMail => linkmail_core
    | TryDeliverOp.UnlinkTmp => Call (MailFSOp.UnlinkTmp)
    | TryDeliverOp.List => Call (MailFSOp.List)
    | TryDeliverOp.Read fn => Call (MailFSOp.Read fn)
    | TryDeliverOp.Delete fn => Call (MailFSOp.Delete fn)
    | TryDeliverOp.Lock => Call (MailFSOp.Lock)
    | TryDeliverOp.Unlock => Call (MailFSOp.Unlock)
    | TryDeliverOp.Ext extop => Call (MailFSOp.Ext extop)
    end.

  (* END CODE *)

  Theorem compile_op_no_atomics :
    forall `(op : _ T),
      no_atomics (compile_op op).
  Proof.
    destruct op; compute; eauto.
  Qed.

  Ltac step_inv :=
    match goal with
    | H : TryDeliverAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : MailFSAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    end; intuition idtac.

  Hint Extern 1 (TryDeliverAPI.step _ _ _ _ _ _) => econstructor.
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
    compile_correct compile_op MailFSAPI.step TryDeliverAPI.step.
  Proof.
    unfold compile_correct; intros.
    destruct op.

    all: repeat atomic_exec_inv; repeat step_inv; eauto.
  Qed.

  Definition initP_compat : forall s, MailFSAPI.initP s ->
                                 TryDeliverAPI.initP s :=
    ltac:(auto).

End TryDeliverImpl'.


Module TryDeliverImpl :=
  LayerImplMovers
    MailboxTmpAbsState
    MailFSOp     MailFSAPI
    TryDeliverOp TryDeliverAPI
    TryDeliverImpl'.

Module TryDeliverImplH' :=
  LayerImplMoversHT
    MailboxTmpAbsState
    MailFSOp     MailFSAPI
    TryDeliverOp TryDeliverAPI
    TryDeliverImpl'
    UserIdx.

Module TryDeliverImplH :=
  LayerImplMovers
    MailboxTmpAbsHState
    MailFSHOp     MailFSHAPI
    TryDeliverHOp TryDeliverHAPI
    TryDeliverImplH'.
