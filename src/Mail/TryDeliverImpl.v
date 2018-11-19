Require Import CSPEC.
Require Import MailServerAPI.
Require Import MailboxAPI.
Require Import TryDeliverAPI.
Require Import MailFSAPI.
Require Import MailboxTmpAbsAPI.


Module TryDeliverImpl'.
  Import Layer.

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
    unfold MailFSAPI.l in *;
    unfold TryDeliverAPI.l in *;
    unfold step in *;
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
      MailFSAPI.l.(step)
      (MailFSOp.Random).
  Proof.
    unfold right_mover; intros.
    repeat step_inv; eauto 10.

    eexists; split; econstructor.
  Qed.

  Hint Resolve random_right_mover.

  Theorem ysa_movers_linkmail_core :
    ysa_movers MailFSAPI.l.(step) linkmail_core.
  Proof.
    econstructor; eauto 20.
  Qed.

  Hint Resolve ysa_movers_linkmail_core.

  Theorem ysa_movers : forall `(op : _ T),
    ysa_movers MailFSAPI.l.(step) (compile_op op).
  Proof.
    destruct op; simpl; eauto 20.
  Qed.

  Theorem compile_correct :
    compile_correct compile_op MailFSAPI.l.(step) TryDeliverAPI.l.(step).
  Proof.
    unfold compile_correct; intros.
    destruct op.

    all: repeat atomic_exec_inv; repeat step_inv; eauto.
  Qed.

  Definition initP_compat : forall s, MailFSAPI.l.(initP) s ->
                                 TryDeliverAPI.l.(initP) s :=
    ltac:(auto).

  Print LayerImplMoversT.t.
  Definition l : LayerImplMoversT.t MailFSAPI.l TryDeliverAPI.l.
    exact {| LayerImplMoversT.compile_op := compile_op;
             LayerImplMoversT.compile_op_no_atomics := @compile_op_no_atomics;
             LayerImplMoversT.ysa_movers := @ysa_movers;
             LayerImplMoversT.compile_correct := compile_correct;
             LayerImplMoversT.initP_compat := initP_compat; |}.
  Defined.
                                                         
End TryDeliverImpl'.

Definition TryDeliverImpl := LayerImplMovers.t TryDeliverImpl'.l.

Definition TryDeliverImplH' := LayerImplMoversHT.t TryDeliverImpl'.l UserIdx.idx.

Definition TryDeliverImplH := LayerImplMovers.t TryDeliverImplH'.
