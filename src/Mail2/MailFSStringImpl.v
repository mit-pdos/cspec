Require Import POCS.
Require Import String.
Require Import MailServerAPI.
Require Import MailFSAPI.
Require Import MailFSStringAPI.
Require Import MailFSStringAbsAPI.


Module MailFSStringImpl <:
  LayerImpl
    MailFSStringOp MailFSStringAbsState MailFSStringAPI
    MailFSOp MailFSStringAbsState MailFSStringAbsAPI.

  Definition createwritetmp_core data :=
    tid <- Op (MailFSStringOp.GetTID);
    r <- Op (MailFSStringOp.CreateWriteTmp (encode_tid_fn tid 0) data);
    Ret r.

  Definition linkmail_core mboxfn :=
    tid <- Op (MailFSStringOp.GetTID);
    v <- Op (MailFSStringOp.LinkMail (encode_tid_fn tid 0) (encode_tid_fn tid mboxfn));
    Ret v.

  Definition unlinktmp_core :=
    tid <- Op (MailFSStringOp.GetTID);
    r <- Op (MailFSStringOp.UnlinkTmp (encode_tid_fn tid 0));
    Ret r.

  Definition list_core :=
    l <- Op (MailFSStringOp.List);
    Ret (map decode_tid_fn l).

  Definition compile_op T (op : MailFSOp.opT T) : proc _ T :=
    match op with
    | MailFSOp.LinkMail m => linkmail_core m
    | MailFSOp.List => list_core
    | MailFSOp.Read fn => Op (MailFSStringOp.Read (encode_tid_fn (fst fn) (snd fn)))
    | MailFSOp.Delete fn => Op (MailFSStringOp.Delete (encode_tid_fn (fst fn) (snd fn)))
    | MailFSOp.CreateWriteTmp data => createwritetmp_core data
    | MailFSOp.UnlinkTmp => unlinktmp_core
    | MailFSOp.Ext extop => Op (MailFSStringOp.Ext extop)
    | MailFSOp.Lock => Op (MailFSStringOp.Lock)
    | MailFSOp.Unlock => Op (MailFSStringOp.Unlock)
    | MailFSOp.GetTID => Op (MailFSStringOp.GetTID)
    | MailFSOp.Random => Op (MailFSStringOp.Random)
    end.

  Ltac step_inv :=
    match goal with
    | H : MailFSStringAbsAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : MailFSStringAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    end; intuition idtac.

  Hint Extern 1 (MailFSStringAbsAPI.step _ _ _ _ _ _) => econstructor.
  Hint Extern 1 (MailFSStringAPI.step _ _ _ _ _ _) => econstructor.

  Lemma gettid_right_mover :
    right_mover
      MailFSStringAPI.step
      (MailFSStringOp.GetTID).
  Proof.
    unfold right_mover; intros.
    repeat step_inv; eauto.

    eexists; split; econstructor.
  Qed.

  Hint Resolve gettid_right_mover.

  Theorem linkmail_atomic : forall `(rx : _ -> proc _ T) m,
    trace_incl MailFSStringAPI.step
      (Bind (compile_op (MailFSOp.LinkMail m)) rx)
      (Bind (atomize compile_op (MailFSOp.LinkMail m)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold linkmail_core, ysa_movers.
    eauto 20.
  Qed.

  Theorem list_atomic : forall `(rx : _ -> proc _ T),
    trace_incl MailFSStringAPI.step
      (Bind (compile_op (MailFSOp.List)) rx)
      (Bind (atomize compile_op (MailFSOp.List)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold list_core, ysa_movers.
    eauto 20.
  Qed.

  Theorem createwritetmp_atomic : forall `(rx : _ -> proc _ T) fn,
    trace_incl MailFSStringAPI.step
      (Bind (compile_op (MailFSOp.CreateWriteTmp fn)) rx)
      (Bind (atomize compile_op (MailFSOp.CreateWriteTmp fn)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold createwritetmp_core, ysa_movers.
    eauto 20.
  Qed.

  Theorem unlinktmp_atomic : forall `(rx : _ -> proc _ T),
    trace_incl MailFSStringAPI.step
      (Bind (compile_op (MailFSOp.UnlinkTmp)) rx)
      (Bind (atomize compile_op (MailFSOp.UnlinkTmp)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold unlinktmp_core, ysa_movers.
    eauto 20.
  Qed.

  Theorem my_compile_correct :
    compile_correct compile_op MailFSStringAPI.step MailFSStringAbsAPI.step.
  Proof.
    unfold compile_correct; intros.
    destruct op.

    all: try solve [ repeat atomic_exec_inv; repeat step_inv; eauto ].

    repeat atomic_exec_inv.
    repeat step_inv; eauto.

    destruct fn; simpl in *.
    eauto.

    destruct fn; simpl in *.
    eauto.
  Qed.

  Theorem my_atomize_correct :
    atomize_correct compile_op MailFSStringAPI.step.
  Proof.
    unfold atomize_correct; intros.
    destruct op; try trace_incl_simple.

    + rewrite createwritetmp_atomic.
      eapply trace_incl_bind_a; eauto.
    + rewrite linkmail_atomic.
      eapply trace_incl_bind_a; eauto.
    + rewrite unlinktmp_atomic.
      eapply trace_incl_bind_a; eauto.
    + rewrite list_atomic.
      eapply trace_incl_bind_a; eauto.
  Qed.

  Hint Resolve my_compile_correct.
  Hint Resolve my_atomize_correct.

  Theorem all_traces_match :
    forall ts1 ts2,
      proc_match (Compile.compile_ok compile_op) ts1 ts2 ->
      traces_match_ts MailFSStringAPI.step MailFSStringAbsAPI.step ts1 ts2.
  Proof.
    intros.
    eapply Compile.compile_traces_match_ts; eauto.
  Qed.

  Definition absR (s1 : MailFSStringAbsState.State) (s2 : MailFSStringAbsState.State) :=
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
        MailFSStringAbsState.initP
        MailFSStringAPI.step
        MailFSStringAbsAPI.step (compile_ts ts2) ts2.
  Proof.
    unfold traces_match_abs; intros.
    rewrite H2 in *; clear H2.
    eapply all_traces_match; eauto.
    eapply Compile.compile_ts_ok; eauto.
  Qed.

  Theorem absInitP :
    forall s1 s2,
      MailFSStringAbsState.initP s1 ->
      absR s1 s2 ->
      MailFSStringAbsState.initP s2.
  Proof.
    eauto.
  Qed.

End MailFSStringImpl.
