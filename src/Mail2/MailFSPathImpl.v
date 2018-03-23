Require Import POCS.
Require Import String.
Require Import MailServerAPI.
Require Import MailFSStringAPI.
Require Import MailFSPathAbsAPI.
Require Import MailFSPathAPI.


Module MailFSPathImpl <:
  LayerImpl
    MailFSPathOp MailFSPathAbsState MailFSPathAPI
    MailFSStringOp MailFSPathAbsState MailFSPathAbsAPI.

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

  Ltac step_inv :=
    match goal with
    | H : MailFSPathAbsAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : MailFSPathAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    end; intuition idtac.

  Hint Extern 1 (MailFSPathAbsAPI.step _ _ _ _ _ _) => econstructor.
  Hint Extern 1 (MailFSPathAPI.step _ _ _ _ _ _) => econstructor.

  Theorem my_compile_correct :
    compile_correct compile_op MailFSPathAPI.step MailFSPathAbsAPI.step.
  Proof.
    unfold compile_correct; intros.
    destruct op.

    all: try solve [ repeat atomic_exec_inv; repeat step_inv; eauto ].
  Qed.

  Theorem my_atomize_correct :
    atomize_correct compile_op MailFSPathAPI.step.
  Proof.
    unfold atomize_correct; intros.
    destruct op; trace_incl_simple.
  Qed.

  Hint Resolve my_compile_correct.
  Hint Resolve my_atomize_correct.

  Theorem all_traces_match :
    forall ts1 ts2,
      proc_match (Compile.compile_ok compile_op) ts1 ts2 ->
      traces_match_ts MailFSPathAPI.step MailFSPathAbsAPI.step ts1 ts2.
  Proof.
    intros.
    eapply Compile.compile_traces_match_ts; eauto.
  Qed.

  Definition absR (s1 : MailFSPathAbsState.State) (s2 : MailFSPathAbsState.State) :=
    s1 = s2.

  Definition compile_ts := Compile.compile_ts compile_op.

  Theorem compile_ts_no_atomics :
    forall ts,
      no_atomics_ts ts ->
      no_atomics_ts (compile_ts ts).
  Proof.
    eapply Compile.compile_ts_no_atomics.
    destruct op; compute; eauto.
  Qed.

  Theorem compile_traces_match :
    forall ts2,
      no_atomics_ts ts2 ->
      traces_match_abs absR
        MailFSPathAbsState.initP
        MailFSPathAPI.step
        MailFSPathAbsAPI.step (compile_ts ts2) ts2.
  Proof.
    unfold traces_match_abs; intros.
    rewrite H2 in *; clear H2.
    eapply all_traces_match; eauto.
    eapply Compile.compile_ts_ok; eauto.
  Qed.

  Theorem absInitP :
    forall s1 s2,
      MailFSPathAbsState.initP s1 ->
      absR s1 s2 ->
      MailFSPathAbsState.initP s2.
  Proof.
    eauto.
  Qed.

End MailFSPathImpl.
