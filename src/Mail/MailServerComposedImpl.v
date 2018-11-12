Require Import CSPEC.
Require Import MailServerAPI.
Require Import MailServerComposedAPI.

Module MailServerComposedImpl'.

  Import MailServerComposedOp.

  (* START CODE *)

  Definition compile_op T (op : MailServerComposedOp.Op T) : proc MailServerHOp T :=
    match op with
    | Deliver u m => Call (Slice u (MailServerOp.Deliver m))
    | Pickup u => Call (Slice u (MailServerOp.Pickup))
    | CheckUser u => Call (CheckSlice (u: UserIdx.idx))
    | Delete u id => Call (Slice u (MailServerOp.Delete id))
    | Ext extop => Call (Slice (nouser: validIndexT UserIdx.idx) (MailServerOp.Ext extop))
    end.

  (* END CODE *)

  Theorem compile_op_no_atomics :
    forall T (op : _ T),
      no_atomics (compile_op op).
  Proof.
    destruct op; simpl; eauto.
  Qed.

  Ltac step_inv :=
    cbn [Layer.step MailServerHAPI] in *;
    cbn [Layer.step MailServerComposedAPI.l] in *;
    match goal with
    | H : MailServerHAPI.(Layer.step) _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : MailServerAPI.l.(Layer.step) _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    end; intuition idtac.

  Hint Constructors MailServerComposedAPI.xstep.

  Print MailServerHAPI.
  Theorem compile_correct :
    compile_correct compile_op MailServerHAPI.(Layer.step) MailServerComposedAPI.l.(Layer.step).
  Proof.
    unfold compile_correct; intros.
    destruct op.
    all: atomic_exec_inv.
    all: repeat step_inv.
    all: unfold MailServerComposedAPI.step.
    all: unfold user in *.
    all: unfold UserIdx.idx in *.
    all: try destruct_validIndex.
    all: try rewrite hadd_hget_eq.
    all: eauto.

    destruct nouser.
    rewrite hadd_hget_eq.
    eauto.
  Qed.

  Theorem ysa_movers : forall `(op : _ T),
    ysa_movers MailServerHAPI.(Layer.step) (compile_op op).
  Proof.
    destruct op; simpl; eauto.
  Qed.

  Definition initP_compat : forall s, MailServerHAPI.(Layer.initP) s ->
                                 MailServerComposedAPI.l.(Layer.initP) s :=
    ltac:(auto).

  Definition l : LayerImplMoversT.t MailServerHAPI MailServerComposedAPI.l.
    refine {| LayerImplMoversT.ysa_movers := @ysa_movers;
              LayerImplMoversT.initP_compat := initP_compat;
              LayerImplMoversT.compile_correct := compile_correct;
              LayerImplMoversT.compile_op := compile_op;
              LayerImplMoversT.compile_op_no_atomics := compile_op_no_atomics; |}.
    Defined.
    
End MailServerComposedImpl'.

Definition MailServerComposedImpl :=
 LayerImplMovers.t MailServerComposedImpl'.l.