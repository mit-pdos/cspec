Require Import POCS.
Require Import String.
Require Import MailServerAPI.
Require Import MailboxAPI.
Require Import DeliverAPI.
Require Import TryDeliverAPI.


Module LinkRetryImpl <: LayerImpl TryDeliverAPI DeliverAPI.

  Definition retry_cond (r : bool) := r.
  Definition once_cond {T} (r : T) := true.

  Definition compile_op T (op : DeliverAPI.opT T) : (T -> TryDeliverAPI.opT T) * (T -> bool) * T :=
    match op with
    | DeliverAPI.CreateWriteTmp data => (fun _ => TryDeliverAPI.CreateWriteTmp data, once_cond, tt)
    | DeliverAPI.LinkMail => (fun _ => TryDeliverAPI.LinkMail, retry_cond, false)
    | DeliverAPI.UnlinkTmp => (fun _ => TryDeliverAPI.UnlinkTmp, once_cond, tt)
    | DeliverAPI.List => (fun _ => TryDeliverAPI.List, once_cond, nil)
    | DeliverAPI.Read fn => (fun _ => TryDeliverAPI.Read fn, once_cond, (Some ""%string))
    | DeliverAPI.GetRequest => (fun _ => TryDeliverAPI.GetRequest, once_cond, MailServerAPI.ReqRead)
    | DeliverAPI.Respond r => (fun _ => TryDeliverAPI.Respond r, once_cond, tt)
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

  Definition absR (s1 : TryDeliverAPI.State) (s2 : DeliverAPI.State) :=
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
      traces_match_abs absR TryDeliverAPI.initP TryDeliverAPI.step DeliverAPI.step (compile_ts ts) ts.
  Proof.
    unfold traces_match_abs, absR; intros; subst.
    eapply CompileLoop.compile_traces_match_ts; eauto.
    eapply noop_or_success.
    eapply CompileLoop.compile_ts_ok; eauto.
  Qed.

  Theorem absInitP :
    forall s1 s2,
      TryDeliverAPI.initP s1 ->
      absR s1 s2 ->
      DeliverAPI.initP s2.
  Proof.
    eauto.
  Qed.

End LinkRetryImpl.
