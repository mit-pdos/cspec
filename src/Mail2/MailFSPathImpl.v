Require Import POCS.
Require Import String.
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
    | MailFSStringOp.LinkMail tmpfn mailfn => Op (MailFSPathOp.Link ("tmp"%string, tmpfn) ("mail"%string, mailfn))
    | MailFSStringOp.List => Op (MailFSPathOp.List "mail"%string)
    | MailFSStringOp.Read fn => Op (MailFSPathOp.Read ("mail"%string, fn))
    | MailFSStringOp.Delete fn => Op (MailFSPathOp.Unlink ("mail"%string, fn))
    | MailFSStringOp.CreateWriteTmp tmpfn data => Op (MailFSPathOp.CreateWrite ("tmp"%string, tmpfn) data)
    | MailFSStringOp.UnlinkTmp tmpfn => Op (MailFSPathOp.Unlink ("tmp"%string, tmpfn))
    | MailFSStringOp.Ext extop => Op (MailFSPathOp.Ext extop)
    | MailFSStringOp.Lock => Op (MailFSPathOp.Lock)
    | MailFSStringOp.Unlock => Op (MailFSPathOp.Unlock)
    | MailFSStringOp.GetTID => Op (MailFSPathOp.GetTID)
    | MailFSStringOp.Random => Op (MailFSPathOp.Random)
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
    all: admit.
  Admitted.

End MailFSPathImpl'.


Module MailFSPathImpl :=
  LayerImplMovers
    MailFSPathAbsState 
    MailFSPathOp MailFSPathAPI
    MailFSStringOp MailFSPathAbsAPI.
