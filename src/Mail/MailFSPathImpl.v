Require Import POCS.
Require Import MailServerAPI.
Require Import MailFSStringAPI.
Require Import MailFSPathAbsAPI.
Require Import MailFSPathAPI.


Module MailFSPathImpl' <:
  LayerImplMoversT
    MailFSPathAbsState 
    MailFSPathOp MailFSPathAPI
    MailFSStringOp MailFSPathAbsAPI.

  Definition compile_op T (op : MailFSStringOp.opT T) : proc _ T :=
    match op with
    | MailFSStringOp.LinkMail tmpfn mailfn => Prim (MailFSPathOp.Link (tmp_string, tmpfn) (mail_string, mailfn))
    | MailFSStringOp.List => Prim (MailFSPathOp.List mail_string)
    | MailFSStringOp.Read fn => Prim (MailFSPathOp.Read (mail_string, fn))
    | MailFSStringOp.Delete fn => Prim (MailFSPathOp.Unlink (mail_string, fn))
    | MailFSStringOp.CreateWriteTmp tmpfn data => Prim (MailFSPathOp.CreateWrite (tmp_string, tmpfn) data)
    | MailFSStringOp.UnlinkTmp tmpfn => Prim (MailFSPathOp.Unlink (tmp_string, tmpfn))
    | MailFSStringOp.Ext extop => Prim (MailFSPathOp.Ext extop)
    | MailFSStringOp.Lock => Prim (MailFSPathOp.Lock)
    | MailFSStringOp.Unlock => Prim (MailFSPathOp.Unlock)
    | MailFSStringOp.GetTID => Prim (MailFSPathOp.GetTID)
    | MailFSStringOp.Random => Prim (MailFSPathOp.Random)
    end.

  Theorem compile_op_no_atomics :
    forall `(op : _ T),
      no_atomics (compile_op op).
  Proof.
    destruct op; compute; eauto.
  Qed.

  Ltac step_inv :=
    match goal with
    | H : MailFSPathAbsAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : MailFSPathAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    end; intuition idtac.

  Hint Extern 1 (MailFSPathAbsAPI.step _ _ _ _ _ _) => econstructor.
  Hint Extern 1 (MailFSPathAPI.step _ _ _ _ _ _) => econstructor.

  Theorem compile_correct :
    compile_correct compile_op MailFSPathAPI.step MailFSPathAbsAPI.step.
  Proof.
    unfold compile_correct; intros.
    destruct op.

    all: try solve [ repeat atomic_exec_inv; repeat step_inv; eauto ].
  Qed.

  Theorem ysa_movers : forall `(op : _ T),
    ysa_movers MailFSPathAPI.step (compile_op op).
  Proof.
    destruct op; simpl; eauto 20.
  Qed.

End MailFSPathImpl'.


Module MailFSPathImpl :=
  LayerImplMovers
    MailFSPathAbsState 
    MailFSPathOp MailFSPathAPI
    MailFSStringOp MailFSPathAbsAPI
    MailFSPathImpl'.

Module MailFSPathImplH' :=
  LayerImplMoversHT
    MailFSPathAbsState 
    MailFSPathOp MailFSPathAPI
    MailFSStringOp MailFSPathAbsAPI
    MailFSPathImpl'
    UserIdx.

Module MailFSPathImplH :=
  LayerImplMovers
    MailFSPathAbsHState 
    MailFSPathHOp MailFSPathHAPI
    MailFSStringHOp MailFSPathAbsHAPI
    MailFSPathImplH'.
