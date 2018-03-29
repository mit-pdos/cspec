Require Import POCS.
Require Import String.
Require Import MailServerAPI.
Require Import MailFSMergedAPI.
Require Import MailFSPathAPI.
Require Import MailFSPathAbsAPI.


Module MailFSMergedAbsImpl' <:
  LayerImplAbsT MailFSPathHOp
    MailFSMergedState   MailFSMergedAbsAPI
    MailFSPathAbsHState MailFSPathHAPI.

  Definition absR (s1 : MailFSMergedState.State) (s2 : MailFSPathAbsHState.State) :=
    True.

  Hint Resolve FMap.add_mapsto.
  Hint Resolve FMap.mapsto_add_ne'.

  Theorem absR_ok :
    op_abs absR MailFSMergedAbsAPI.step MailFSPathHAPI.step.
  Proof.
    unfold op_abs; intros.
  Admitted.

  Theorem absInitP :
    forall s1 s2,
      MailFSMergedState.initP s1 ->
      absR s1 s2 ->
      MailFSPathAbsHState.initP s2.
  Proof.
  Admitted.

End MailFSMergedAbsImpl'.


Module MailFSMergedAbsImpl :=
 LayerImplAbs MailFSPathHOp
    MailFSMergedState   MailFSMergedAbsAPI
    MailFSPathAbsHState MailFSPathHAPI
    MailFSMergedAbsImpl'.


Module MailFSMergedOpImpl' <:
  LayerImplMoversT
    MailFSMergedState
    MailFSMergedOp MailFSMergedAPI
    MailFSPathHOp  MailFSMergedAbsAPI.

  Import MailFSPathOp.

  Definition compile_op T (op : MailFSPathHOp.opT T) : proc _ T :=
    match op with
    | Slice u op' =>
      match op' with
      | Link (srcdir, srcfn) (dstdir, dstfn) =>
        Op (MailFSMergedOp.Link (u, srcdir, srcfn) (u, dstdir, dstfn))
      | List dir =>
        Op (MailFSMergedOp.List (u, dir))
      | Read (dir, fn) =>
        Op (MailFSMergedOp.Read (u, dir, fn))
      | CreateWrite (dir, fn) data =>
        Op (MailFSMergedOp.CreateWrite (u, dir, fn) data)
      | Unlink (dir, fn) =>
        Op (MailFSMergedOp.Unlink (u, dir, fn))
      | Ext extop =>
        Op (MailFSMergedOp.Ext extop)
      | Lock =>
        Op (MailFSMergedOp.Lock u)
      | Unlock =>
        Op (MailFSMergedOp.Unlock u)
      | GetTID =>
        Op (MailFSMergedOp.GetTID)
      | Random =>
        Op (MailFSMergedOp.Random)
      end
    | CheckSlice u =>
      Op (MailFSMergedOp.Exists u)
    end.

  Ltac break_pairs :=
    match goal with
    | x : ?T * ?R |- _ => destruct x
    end.

  Theorem compile_op_no_atomics :
    forall `(op : _ T),
      no_atomics (compile_op op).
  Proof.
    destruct op; simpl; eauto.
    destruct op; compute; eauto.
    all: repeat break_pairs; eauto.
  Qed.

  Ltac step_inv :=
    match goal with
    | H : MailFSMergedAbsAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : MailFSMergedAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    end; intuition idtac.

  Hint Extern 1 (MailFSMergedAbsAPI.step _ _ _ _ _ _) => econstructor.
  Hint Extern 1 (MailFSMergedAPI.step _ _ _ _ _ _) => econstructor.

  Theorem compile_correct :
    compile_correct compile_op MailFSMergedAPI.step MailFSMergedAbsAPI.step.
  Proof.
    unfold compile_correct; intros.
    destruct op.
    destruct op.
    all: repeat break_pairs.
    all: repeat atomic_exec_inv.
    all: repeat step_inv.
    all: eauto.
  Qed.

  Theorem ysa_movers : forall `(op : _ T),
    ysa_movers MailFSMergedAPI.step (compile_op op).
  Proof.
    destruct op; simpl; eauto.
    destruct op; simpl; repeat break_pairs; eauto 20.
  Qed.

End MailFSMergedOpImpl'.


Module MailFSMergedOpImpl :=
  LayerImplMovers
    MailFSMergedState
    MailFSMergedOp MailFSMergedAPI
    MailFSPathHOp  MailFSMergedAbsAPI
    MailFSMergedOpImpl'.

Module MailFSMergedImpl :=
  Link
    MailFSMergedOp MailFSMergedState   MailFSMergedAPI
    MailFSPathHOp  MailFSMergedState   MailFSMergedAbsAPI
    MailFSPathHOp  MailFSPathAbsHState MailFSPathHAPI
    MailFSMergedOpImpl MailFSMergedAbsImpl.
