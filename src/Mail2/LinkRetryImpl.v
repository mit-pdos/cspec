Require Import POCS.
Require Import String.
Require Import MailServerAPI.
Require Import MailboxAPI.
Require Import MailboxTmpAbsAPI.
Require Import DeliverAPI.
Require Import TryDeliverAPI.


Module LinkRetryImpl' <:
  LayerImplLoopT
    MailboxTmpAbsState
    TryDeliverOp TryDeliverAPI
    DeliverOp DeliverAPI.

  Definition retry_cond (r : bool) := r.
  Definition once_cond {T} (r : T) := true.

  Definition compile_op T (op : DeliverOp.opT T) : (option T -> TryDeliverOp.opT T) * (T -> bool) * option T :=
    match op with
    | DeliverOp.CreateWriteTmp data => (fun _ => TryDeliverOp.CreateWriteTmp data, once_cond, None)
    | DeliverOp.LinkMail => (fun _ => TryDeliverOp.LinkMail, retry_cond, None)
    | DeliverOp.UnlinkTmp => (fun _ => TryDeliverOp.UnlinkTmp, once_cond, None)
    | DeliverOp.List => (fun _ => TryDeliverOp.List, once_cond, None)
    | DeliverOp.Read fn => (fun _ => TryDeliverOp.Read fn, once_cond, None)
    | DeliverOp.Delete fn => (fun _ => TryDeliverOp.Delete fn, once_cond, None)
    | DeliverOp.Lock => (fun _ => TryDeliverOp.Lock, once_cond, None)
    | DeliverOp.Unlock => (fun _ => TryDeliverOp.Unlock, once_cond, None)
    | DeliverOp.Ext extop => (fun _ => TryDeliverOp.Ext extop, once_cond, None)
    end.

  Ltac step_inv :=
    match goal with
    | H : TryDeliverAPI.xstep _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : DeliverAPI.xstep _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    end.

  Ltac pair_inv :=
    match goal with
    | H : (_, _) = (_, _) |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    end.

  Hint Constructors TryDeliverAPI.xstep.
  Hint Constructors DeliverAPI.xstep.

  Theorem noop_or_success :
    noop_or_success compile_op TryDeliverAPI.step DeliverAPI.step.
  Proof.
    unfold noop_or_success.
    unfold TryDeliverAPI.step, DeliverAPI.step.
    destruct opM; simpl; intros; pair_inv; step_inv; eauto.
  Qed.

End LinkRetryImpl'.

Module LinkRetryImpl :=
  LayerImplLoop
    MailboxTmpAbsState
    TryDeliverOp TryDeliverAPI
    DeliverOp DeliverAPI
    LinkRetryImpl'.

Module LinkRetryImplH' :=
  LayerImplLoopHT
    MailboxTmpAbsState
    TryDeliverOp TryDeliverAPI
    DeliverOp DeliverAPI
    LinkRetryImpl'
    UserIdx.

Module LinkRetryImplH :=
  LayerImplLoop
    MailboxTmpAbsHState
    TryDeliverHOp TryDeliverHAPI
    DeliverHOp DeliverHAPI
    LinkRetryImplH'.
