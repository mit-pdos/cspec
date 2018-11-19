Require Import CSPEC.
Require Import MailServerAPI.
Require Import MailboxAPI.
Require Import MailboxTmpAbsAPI.
Require Import DeliverAPI.
Require Import TryDeliverAPI.


Module LinkRetryImpl'.
  Import Layer.

  (* START CODE *)

  Definition retry_cond (r : bool) := r.
  Definition once_cond {T} (r : T) := true.

  Definition compile_op T (op : DeliverOp.Op T) : (option T -> TryDeliverOp.Op T) * (T -> bool) * option T :=
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

  (* END CODE *)

  Ltac step_inv :=
    unfold DeliverAPI.l in *;
    unfold TryDeliverAPI.l in *;
    unfold DeliverAPI.step in *;
    unfold TryDeliverAPI.step in *;
    unfold step in *;
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
    noop_or_success compile_op TryDeliverAPI.l.(step) DeliverAPI.l.(step).
  Proof.
    unfold noop_or_success.
    destruct opM; simpl; intros; pair_inv; step_inv; eauto.
  Qed.

  Definition initP_compat : forall s, TryDeliverAPI.l.(initP) s ->
                                 DeliverAPI.l.(initP) s :=
    ltac:(auto).
 
  Definition l : LayerImplLoopT.t TryDeliverAPI.l DeliverAPI.l.
    exact {| LayerImplLoopT.compile_op := compile_op;
             LayerImplLoopT.noop_or_success := noop_or_success;
             LayerImplLoopT.initP_compat := initP_compat; |}.
  Defined.

End LinkRetryImpl'.

Definition LinkRetryImpl := LayerImplLoop.t LinkRetryImpl'.l.

Definition LinkRetryImplH' := LayerImplLoopHT.t LinkRetryImpl'.l UserIdx.idx.

Definition LinkRetryImplH := LayerImplLoop.t LinkRetryImplH'.
