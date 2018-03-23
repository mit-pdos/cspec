Require Import POCS.
Require Import String.
Require Import MailServerAPI.
Require Import MailboxAPI.
Require Import MailboxTmpAbsAPI.
Require Import DeliverAPI.
Require Import TryDeliverAPI.


Module LinkRetryImpl <:
  LayerImpl
    TryDeliverOp MailboxTmpAbsState TryDeliverAPI
    DeliverOp  MailboxTmpAbsState DeliverAPI.

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

  Definition compile_ts ts :=
    CompileLoop.compile_ts compile_op ts.

  Theorem compile_ts_no_atomics :
    forall ts,
      no_atomics_ts ts ->
      no_atomics_ts (compile_ts ts).
  Proof.
    eapply CompileLoop.compile_ts_no_atomics.
  Qed.

  Definition absR (s1 : MailboxTmpAbsState.State) (s2 : MailboxTmpAbsState.State) :=
    s1 = s2.

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

  Theorem compile_traces_match :
    forall ts,
      no_atomics_ts ts ->
      traces_match_abs absR MailboxTmpAbsState.initP TryDeliverAPI.step DeliverAPI.step (compile_ts ts) ts.
  Proof.
    unfold traces_match_abs, absR; intros; subst.
    eapply CompileLoop.compile_traces_match_ts; eauto.
    eapply noop_or_success.
    eapply CompileLoop.compile_ts_ok; eauto.
  Qed.

  Theorem absInitP :
    forall s1 s2,
      MailboxTmpAbsState.initP s1 ->
      absR s1 s2 ->
      MailboxTmpAbsState.initP s2.
  Proof.
    eauto.
  Qed.

End LinkRetryImpl.
