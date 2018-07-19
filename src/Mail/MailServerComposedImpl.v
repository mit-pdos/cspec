Require Import CSPEC.
Require Import MailServerAPI.
Require Import MailServerComposedAPI.

Module MailServerComposedImpl' <:
  LayerImplMoversT
    MailServerComposedState
    MailServerHOp        MailServerHAPI
    MailServerComposedOp MailServerComposedAPI.

  Import MailServerComposedOp.

  Definition compile_op T (op : MailServerComposedOp.Op T) : proc MailServerHOp.Op T :=
    match op with
    | Deliver u m => Call (Slice u (MailServerOp.Deliver m))
    | Pickup u => Call (Slice u (MailServerOp.Pickup))
    | CheckUser u => Call (CheckSlice u)
    | Delete u id => Call (Slice u (MailServerOp.Delete id))
    | Ext extop => Call (Slice nouser (MailServerOp.Ext extop))
    end.

  Theorem compile_op_no_atomics :
    forall `(op : _ T),
      no_atomics (compile_op op).
  Proof.
    destruct op; simpl; eauto.
  Qed.

  Ltac step_inv :=
    match goal with
    | H : MailServerHAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : MailServerAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    end; intuition idtac.

  Hint Constructors MailServerComposedAPI.xstep.

  Theorem compile_correct :
    compile_correct compile_op MailServerHAPI.step MailServerComposedAPI.step.
  Proof.
    unfold compile_correct; intros.
    destruct op.
    all: atomic_exec_inv.
    all: repeat step_inv.
    all: unfold MailServerComposedAPI.step.
    all: unfold user in *.
    all: unfold UserIdx.indexT in *.
    all: repeat sigT_eq.
    all: try destruct_validIndex.
    all: try rewrite hadd_hget_eq.
    all: eauto.

    destruct nouser.
    rewrite hadd_hget_eq.
    eauto.
  Qed.

  Theorem ysa_movers : forall `(op : _ T),
    ysa_movers MailServerHAPI.step (compile_op op).
  Proof.
    destruct op; simpl; eauto.
  Qed.

End MailServerComposedImpl'.

Module MailServerComposedImpl :=
  LayerImplMovers
    MailServerComposedState
    MailServerHOp        MailServerHAPI
    MailServerComposedOp MailServerComposedAPI
    MailServerComposedImpl'.
