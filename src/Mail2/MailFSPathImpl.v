Require Import POCS.
Require Import String.
Require Import MailServerAPI.
Require Import MailFSStringAPI.
Require Import MailFSPathAbsAPI.
Require Import MailFSPathAPI.


Module MailFSPathImpl <: LayerImpl MailFSPathAPI MailFSPathAbsAPI.

  Definition compile_op T (op : MailFSPathAbsAPI.opT T) : proc _ T :=
    match op with
    | MailFSStringAPI.LinkMail tmpfn mailfn => Op (MailFSPathAPI.Link ("tmp"%string, tmpfn) ("mail"%string, mailfn))
    | MailFSStringAPI.List => Op (MailFSPathAPI.List "mail"%string)
    | MailFSStringAPI.Read fn => Op (MailFSPathAPI.Read ("mail"%string, fn))
    | MailFSStringAPI.Delete fn => Op (MailFSPathAPI.Unlink ("mail"%string, fn))
    | MailFSStringAPI.CreateWriteTmp tmpfn data => Op (MailFSPathAPI.CreateWrite ("tmp"%string, tmpfn) data)
    | MailFSStringAPI.UnlinkTmp tmpfn => Op (MailFSPathAPI.Unlink ("tmp"%string, tmpfn))
    | MailFSStringAPI.Ext extop => Op (MailFSPathAPI.Ext extop)
    | MailFSStringAPI.Lock => Op (MailFSPathAPI.Lock)
    | MailFSStringAPI.Unlock => Op (MailFSPathAPI.Unlock)
    | MailFSStringAPI.GetTID => Op (MailFSPathAPI.GetTID)
    | MailFSStringAPI.Random => Op (MailFSPathAPI.Random)
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

  Definition absR (s1 : MailFSPathAPI.State) (s2 : MailFSPathAbsAPI.State) :=
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
        MailFSPathAPI.initP
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
      MailFSPathAPI.initP s1 ->
      absR s1 s2 ->
      MailFSPathAbsAPI.initP s2.
  Proof.
    eauto.
  Qed.

End MailFSPathImpl.
