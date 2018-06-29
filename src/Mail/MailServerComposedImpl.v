Require Import POCS.
Require Import MailServerAPI.
Require Import MailServerComposedAPI.


Axiom nouser : validIndexT UserIdx.indexValid.

Module MailServerComposedImpl' <:
  LayerImplMoversT
    MailServerComposedState
    MailServerHOp        MailServerHAPI
    MailServerComposedOp MailServerComposedAPI.

  Import MailServerComposedOp.

  Definition compile_op T (op : MailServerComposedOp.Op T) : proc MailServerHOp.Op T :=
    match op with
    | Deliver u m => Prim (Slice u (MailServerOp.Deliver m))
    | Pickup u => Prim (Slice u (MailServerOp.Pickup))
    | CheckUser u => Prim (CheckSlice u)
    | Delete u id => Prim (Slice u (MailServerOp.Delete id))
    | Ext extop => Prim (Slice nouser (MailServerOp.Ext extop))
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

    generalize nouser; intros.
    destruct_validIndex.
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
