Require Import CSPEC.
Require Import MailServerAPI.
Require Import MailFSStringAPI.
Require Import MailFSPathAbsAPI.
Require Import MailFSPathAPI.


Module MailFSPathImpl'.
  Import Layer.

  (* START CODE *)

  Definition compile_op T (op : MailFSStringOp.Op T) : proc _ T :=
    match op with
    | MailFSStringOp.LinkMail tmpfn mailfn => Call (MailFSPathOp.Link (tmp_string, tmpfn) (mail_string, mailfn))
    | MailFSStringOp.List => Call (MailFSPathOp.List mail_string)
    | MailFSStringOp.Read fn => Call (MailFSPathOp.Read (mail_string, fn))
    | MailFSStringOp.Delete fn => Call (MailFSPathOp.Unlink (mail_string, fn))
    | MailFSStringOp.CreateWriteTmp tmpfn data => Call (MailFSPathOp.CreateWrite (tmp_string, tmpfn) data)
    | MailFSStringOp.UnlinkTmp tmpfn => Call (MailFSPathOp.Unlink (tmp_string, tmpfn))
    | MailFSStringOp.Ext extop => Call (MailFSPathOp.Ext extop)
    | MailFSStringOp.Lock => Call (MailFSPathOp.Lock)
    | MailFSStringOp.Unlock => Call (MailFSPathOp.Unlock)
    | MailFSStringOp.GetTID => Call (MailFSPathOp.GetTID)
    | MailFSStringOp.Random => Call (MailFSPathOp.Random)
    end.

  (* END CODE *)

  Theorem compile_op_no_atomics :
    forall `(op : _ T),
      no_atomics (compile_op op).
  Proof.
    destruct op; compute; eauto.
  Qed.

  Ltac step_inv :=
    unfold MailFSPathAbsAPI.l in *;
    unfold MailFSPathAPI.l in *;
    unfold step in *;
    match goal with
    | H : MailFSPathAbsAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : MailFSPathAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    end; intuition idtac.

  Hint Extern 1 (MailFSPathAbsAPI.step _ _ _ _ _ _) => econstructor.
  Hint Extern 1 (MailFSPathAPI.step _ _ _ _ _ _) => econstructor.

  Theorem compile_correct :
    compile_correct compile_op MailFSPathAPI.l.(step) MailFSPathAbsAPI.l.(step).
  Proof.
    unfold compile_correct; intros.
    destruct op.

    all: try solve [ repeat atomic_exec_inv; repeat step_inv; eauto ].
  Qed.

  Theorem ysa_movers : forall `(op : _ T),
    ysa_movers MailFSPathAPI.l.(step) (compile_op op).
  Proof.
    destruct op; simpl; eauto 20.
  Qed.

  Definition initP_compat : forall s, MailFSPathAPI.l.(initP) s ->
                                 MailFSPathAbsAPI.l.(initP) s :=
    ltac:(auto).

  Definition l: LayerImplMoversT.t MailFSPathAPI.l MailFSPathAbsAPI.l.
    exact {| LayerImplMoversT.compile_op := compile_op;
             LayerImplMoversT.compile_op_no_atomics := @compile_op_no_atomics;
             LayerImplMoversT.compile_correct := compile_correct;
             LayerImplMoversT.ysa_movers := @ysa_movers;
             LayerImplMoversT.initP_compat := initP_compat; |}.
  Defined.

End MailFSPathImpl'.

Definition MailFSPathImpl := LayerImplMovers.t MailFSPathImpl'.l.

Definition MailFSPathImplH' := LayerImplMoversHT.t MailFSPathImpl'.l UserIdx.idx.

Definition MailFSPathImplH := LayerImplMovers.t MailFSPathImplH'.
