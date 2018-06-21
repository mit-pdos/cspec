Require Import ConcurProc.
Require Import Equiv.
Require Import Compile.
Require Import Abstraction.
Require Import Movers.
Require Import Protocol.
Require Import CompileLoop.
Require Import Helpers.Helpers.


(** Combining trace matching with state abstraction. *)

Section TraceAbs.

  Variable opLoT : Type -> Type.
  Variable opMidT : Type -> Type.

  Variable StateLo : Type.
  Variable StateMid : Type.
  Variable absR : StateLo -> StateMid -> Prop.
  Variable initP : StateLo -> Prop.

  Variable lo_step : OpSemantics opLoT StateLo.
  Variable mid_step : OpSemantics opMidT StateMid.

  Definition traces_match_abs
                           (ts1 : @threads_state opLoT)
                           (ts2 : @threads_state opMidT) :=
    forall (sl : StateLo) (sm : StateMid) tr1,
      initP sl ->
      exec_prefix lo_step sl ts1 tr1 ->
      absR sl sm ->
      exec_prefix mid_step sm ts2 tr1.

End TraceAbs.


Module Type Ops.

  Axiom opT : Type -> Type.

End Ops.


Module Type State.

  Axiom State : Type.
  Axiom initP : State -> Prop.

End State.


Module Type Layer (o : Ops) (s : State).

  Axiom step : OpSemantics o.opT s.State.

End Layer.


Module Type ProcRule (o : Ops).

  Axiom follows_protocol : @threads_state o.opT -> Prop.

End ProcRule.


Module Type Protocol (o : Ops) (s : State).

  Axiom step_allow : forall T, o.opT T -> nat -> s.State -> Prop.

End Protocol.


Module Type LayerImpl
  (o1 : Ops) (s1 : State) (l1 : Layer o1 s1)
  (o2 : Ops) (s2 : State) (l2 : Layer o2 s2).

  Axiom absR : s1.State -> s2.State -> Prop.
  Axiom compile_ts : @threads_state o2.opT -> @threads_state o1.opT.
  Axiom compile_ts_no_atomics :
    forall ts,
      no_atomics_ts ts ->
      no_atomics_ts (compile_ts ts).
  Axiom absInitP :
    forall s1 s2,
      s1.initP s1 ->
      absR s1 s2 ->
      s2.initP s2.
  Axiom compile_traces_match :
    forall ts,
      no_atomics_ts ts ->
      traces_match_abs absR s1.initP l1.step l2.step (compile_ts ts) ts.

  Hint Resolve absInitP.

End LayerImpl.


Module Type LayerImplRequiresRule
  (o1 : Ops) (s1 : State) (l1 : Layer o1 s1)
  (o2 : Ops) (s2 : State) (l2 : Layer o2 s2)
  (r : ProcRule o2).

  Axiom absR : s1.State -> s2.State -> Prop.
  Axiom compile_ts : @threads_state o2.opT -> @threads_state o1.opT.
  Axiom compile_ts_no_atomics :
    forall ts,
      no_atomics_ts ts ->
      no_atomics_ts (compile_ts ts).
  Axiom absInitP :
    forall s1 s2,
      s1.initP s1 ->
      absR s1 s2 ->
      s2.initP s2.
  Axiom compile_traces_match :
    forall ts,
      r.follows_protocol ts ->
      no_atomics_ts ts ->
      traces_match_abs absR s1.initP l1.step l2.step (compile_ts ts) ts.

  Hint Resolve absInitP.

End LayerImplRequiresRule.


Module Type LayerImplFollowsRule
  (o1 : Ops) (s1 : State) (l1 : Layer o1 s1)
  (o2 : Ops) (s2 : State) (l2 : Layer o2 s2)
  (r : ProcRule o1).

  Include (LayerImpl o1 s1 l1 o2 s2 l2).

  Axiom compile_ts_follows_protocol :
    forall ts,
      no_atomics_ts ts ->
      r.follows_protocol (compile_ts ts).

End LayerImplFollowsRule.


Module Type LayerImplAbsT
  (o : Ops)
  (s1 : State) (l1 : Layer o s1)
  (s2 : State) (l2 : Layer o s2).

  Axiom absR : s1.State -> s2.State -> Prop.
  Axiom absR_ok : op_abs absR l1.step l2.step.
  Axiom absInitP :
    forall s1 s2,
      s1.initP s1 ->
      absR s1 s2 ->
      s2.initP s2.

End LayerImplAbsT.


Module LayerImplAbs
  (o : Ops)
  (s1 : State) (l1 : Layer o s1)
  (s2 : State) (l2 : Layer o s2)
  (a : LayerImplAbsT o s1 l1 s2 l2) <: LayerImpl o s1 l1 o s2 l2.

  Definition absR := a.absR.
  Definition absInitP := a.absInitP.

  Definition compile_ts (ts : @threads_state o.opT) := ts.

  Theorem compile_ts_no_atomics :
    forall (ts : @threads_state o.opT),
      no_atomics_ts ts ->
      no_atomics_ts (compile_ts ts).
  Proof.
    unfold compile_ts; eauto.
  Qed.

  Hint Resolve a.absR_ok.

  Theorem compile_traces_match :
    forall ts,
      no_atomics_ts ts ->
      traces_match_abs absR s1.initP l1.step l2.step (compile_ts ts) ts.
  Proof.
    unfold compile_ts, traces_match_abs; intros.
    eapply trace_incl_abs; eauto.
  Qed.

End LayerImplAbs.


Module Type LayerImplMoversT
  (s : State)
  (o1 : Ops) (l1 : Layer o1 s)
  (o2 : Ops) (l2 : Layer o2 s).

  Axiom compile_op : forall T, o2.opT T -> proc o1.opT T.

  Axiom compile_op_no_atomics : forall T (op : o2.opT T),
    no_atomics (compile_op op).

  Axiom ysa_movers : forall T (op : o2.opT T),
    ysa_movers l1.step (compile_op op).

  Axiom compile_correct :
    compile_correct compile_op l1.step l2.step.

End LayerImplMoversT.


Module LayerImplMovers
  (s : State)
  (o1 : Ops) (l1 : Layer o1 s)
  (o2 : Ops) (l2 : Layer o2 s)
  (a : LayerImplMoversT s o1 l1 o2 l2) <: LayerImpl o1 s l1 o2 s l2.

  Definition absR (s1 : s.State) (s2 : s.State) := s1 = s2.

  Theorem absInitP :
    forall s1 s2,
      s.initP s1 ->
      absR s1 s2 ->
      s.initP s2.
  Proof.
    congruence.
  Qed.


  Definition compile_ts := Compile.compile_ts a.compile_op.

  Theorem compile_ts_no_atomics :
    forall ts,
      no_atomics_ts ts ->
      no_atomics_ts (compile_ts ts).
  Proof.
    eapply Compile.compile_ts_no_atomics.
    eapply a.compile_op_no_atomics.
  Qed.

  Theorem op_atomic : forall `(op : o2.opT T) `(rx : _ -> proc _ R),
    trace_incl l1.step
      (Bind (a.compile_op op) rx)
      (Bind (atomize a.compile_op op) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    eapply a.ysa_movers.
  Qed.

  Theorem atomize_correct :
    atomize_correct a.compile_op l1.step.
  Proof.
    unfold atomize_correct; intros.
    rewrite op_atomic.
    eapply trace_incl_bind_a.
    eauto.
  Qed.

  Hint Resolve a.compile_correct.
  Hint Resolve atomize_correct.

  Theorem all_traces_match :
    forall ts1 ts2,
      proc_match (Compile.compile_ok a.compile_op) ts1 ts2 ->
      traces_match_ts l1.step l2.step ts1 ts2.
  Proof.
    intros.
    eapply Compile.compile_traces_match_ts; eauto.
  Qed.

  Theorem compile_traces_match :
    forall ts2,
      no_atomics_ts ts2 ->
      traces_match_abs absR s.initP l1.step l2.step (compile_ts ts2) ts2.
  Proof.
    unfold traces_match_abs; intros.
    rewrite H2 in *; clear H2.
    eapply all_traces_match; eauto.
    eapply Compile.compile_ts_ok; eauto.
  Qed.

End LayerImplMovers.


Module Type LayerImplMoversProtocolT
  (s : State)
  (o1 : Ops) (l1raw : Layer o1 s) (l1 : Layer o1 s)
  (o2 : Ops) (l2 : Layer o2 s)
  (p : Protocol o1 s).

  Include (LayerImplMoversT s o1 l1 o2 l2).

  Axiom op_follows_protocol : forall tid s `(op : o2.opT T),
    follows_protocol_proc l1raw.step p.step_allow tid s (compile_op op).

  Axiom allowed_stable :
    forall `(op : o1.opT T) `(op' : o1.opT T') tid tid' s s' r evs,
      tid <> tid' ->
      p.step_allow op tid s ->
      l1.step op' tid' s r s' evs ->
      p.step_allow op tid s'.

  (* This means that l1.step is either restricted_step or nilpotent_step *)
  Axiom raw_step_ok :
    forall `(op : o1.opT T) tid s r s' evs,
      restricted_step l1raw.step p.step_allow op tid s r s' evs ->
      l1.step op tid s r s' evs.

End LayerImplMoversProtocolT.


Module LayerImplMoversProtocol
  (s : State)
  (o1 : Ops) (l1raw : Layer o1 s) (l1 : Layer o1 s)
  (o2 : Ops) (l2 : Layer o2 s)
  (p : Protocol o1 s)
  (a : LayerImplMoversProtocolT s o1 l1raw l1 o2 l2 p) <: LayerImpl o1 s l1raw o2 s l2.

  Definition absR (s1 : s.State) (s2 : s.State) := s1 = s2.

  Theorem absInitP :
    forall s1 s2,
      s.initP s1 ->
      absR s1 s2 ->
      s.initP s2.
  Proof.
    congruence.
  Qed.


  Definition compile_ts := Compile.compile_ts a.compile_op.

  Theorem compile_ts_no_atomics :
    forall ts,
      no_atomics_ts ts ->
      no_atomics_ts (compile_ts ts).
  Proof.
    eapply Compile.compile_ts_no_atomics.
    eapply a.compile_op_no_atomics.
  Qed.

  Theorem op_atomic : forall `(op : o2.opT T) `(rx : _ -> proc _ R),
    trace_incl l1.step
      (Bind (a.compile_op op) rx)
      (Bind (atomize a.compile_op op) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    eapply a.ysa_movers.
  Qed.

  Theorem atomize_correct :
    atomize_correct a.compile_op l1.step.
  Proof.
    unfold atomize_correct; intros.
    rewrite op_atomic.
    eapply trace_incl_bind_a.
    eauto.
  Qed.

  Hint Resolve a.compile_correct.
  Hint Resolve atomize_correct.

  Theorem all_traces_match :
    forall ts1 ts2,
      proc_match (Compile.compile_ok a.compile_op) ts1 ts2 ->
      traces_match_ts l1.step l2.step ts1 ts2.
  Proof.
    intros.
    eapply Compile.compile_traces_match_ts; eauto.
  Qed.

  Theorem compile_traces_match_l1 :
    forall ts2,
      no_atomics_ts ts2 ->
      traces_match_abs absR s.initP l1.step l2.step (compile_ts ts2) ts2.
  Proof.
    unfold traces_match_abs; intros.
    rewrite H2 in *; clear H2.
    eapply all_traces_match; eauto.
    eapply Compile.compile_ts_ok; eauto.
  Qed.

  Definition follows_protocol (ts : @threads_state o1.opT) :=
    forall s,
      follows_protocol_s l1raw.step p.step_allow ts s.

  Theorem compile_ts_follows_protocol :
    forall ts,
      no_atomics_ts ts ->
      follows_protocol (Compile.compile_ts a.compile_op ts).
  Proof.
    unfold follows_protocol.
    unfold follows_protocol_s.
    intros.
    eapply compile_ts_follows_protocol_proc; try eassumption.
    intros.

    eapply a.op_follows_protocol.
  Qed.

  Theorem compile_traces_match_l1raw :
    forall ts,
      follows_protocol ts ->
      no_atomics_ts ts ->
      traces_match_abs absR s.initP l1raw.step l1.step ts ts.
  Proof.
    unfold compile_ts, follows_protocol, absR.
    unfold traces_match_abs; intros; subst.
    clear H1.
    specialize (H sm).
    destruct H2.
    induction H1; eauto.
    specialize (H tid _ p) as Htid.
    intuition idtac; repeat deex.

    edestruct IHexec.
      eapply follows_protocol_s_exec_tid_upd; eauto.
      intros; eapply a.allowed_stable; eauto.
      eapply a.raw_step_ok; eauto.
      destruct result; eauto.

    eapply ExecPrefixOne.
      eauto.
      eapply exec_tid_step_impl.
      intros; apply a.raw_step_ok; eauto.
      eapply follows_protocol_preserves_exec_tid'; eauto.
      eauto.
  Qed.

  Theorem compile_traces_match :
    forall ts,
      no_atomics_ts ts ->
      traces_match_abs absR s.initP l1raw.step l2.step (compile_ts ts) ts.
  Proof.
    unfold traces_match_abs; intros.
    rewrite H2 in *; clear H2.
    edestruct compile_traces_match_l1raw.
      eapply compile_ts_follows_protocol.
      eassumption.
      eapply Compile.compile_ts_no_atomics.
      eapply a.compile_op_no_atomics.
      eassumption.
      eassumption.
      eassumption.
      reflexivity.
    intuition idtac.
    edestruct compile_traces_match_l1.
      eassumption.
      eassumption.
      eauto.
      reflexivity.
    eexists; intuition eauto.
  Qed.

End LayerImplMoversProtocol.


Module Type LayerImplLoopT
  (s : State)
  (o1 : Ops) (l1 : Layer o1 s)
  (o2 : Ops) (l2 : Layer o2 s).

  Axiom compile_op : forall T, o2.opT T -> (option T -> o1.opT T) * (T -> bool) * option T.
  Axiom noop_or_success :
    noop_or_success compile_op l1.step l2.step.

End LayerImplLoopT.


Module LayerImplLoop
  (s : State)
  (o1 : Ops) (l1 : Layer o1 s)
  (o2 : Ops) (l2 : Layer o2 s)
  (a : LayerImplLoopT s o1 l1 o2 l2) <: LayerImpl o1 s l1 o2 s l2.

  Definition absR (s1 : s.State) (s2 : s.State) := s1 = s2.

  Definition compile_ts ts :=
    CompileLoop.compile_ts a.compile_op ts.

  Theorem compile_ts_no_atomics :
    forall ts,
      no_atomics_ts ts ->
      no_atomics_ts (compile_ts ts).
  Proof.
    eapply CompileLoop.compile_ts_no_atomics.
  Qed.

  Theorem absInitP :
    forall s1 s2,
      s.initP s1 ->
      absR s1 s2 ->
      s.initP s2.
  Proof.
    congruence.
  Qed.

  Theorem compile_traces_match :
    forall ts,
      no_atomics_ts ts ->
      traces_match_abs absR s.initP l1.step l2.step (compile_ts ts) ts.
  Proof.
    unfold traces_match_abs, absR; intros; subst.
    eapply CompileLoop.compile_traces_match_ts; eauto.
    eapply a.noop_or_success.
    eapply CompileLoop.compile_ts_ok; eauto.
  Qed.

End LayerImplLoop.


(** General layer transformers. *)

Module Link
  (oA : Ops) (sA : State) (a : Layer oA sA)
  (oB : Ops) (sB : State) (b : Layer oB sB)
  (oC : Ops) (sC : State) (c : Layer oC sC)
  (x : LayerImpl oA sA a oB sB b)
  (y : LayerImpl oB sB b oC sC c) <: LayerImpl oA sA a oC sC c.

  Definition absR (s1 : sA.State) (s3 : sC.State) :=
    exists s2, x.absR s1 s2 /\ y.absR s2 s3.

  Definition compile_ts ts :=
    x.compile_ts (y.compile_ts ts).

  Theorem compile_ts_no_atomics :
    forall ts,
      no_atomics_ts ts ->
      no_atomics_ts (compile_ts ts).
  Proof.
    intros.
    eapply x.compile_ts_no_atomics.
    eapply y.compile_ts_no_atomics.
    eauto.
  Qed.

  Theorem absInitP :
    forall s1 s2,
      sA.initP s1 ->
      absR s1 s2 ->
      sC.initP s2.
  Proof.
    unfold absR; intros; deex.
    eauto.
  Qed.

  Theorem compile_traces_match :
    forall ts,
      no_atomics_ts ts ->
      traces_match_abs absR sA.initP a.step c.step (compile_ts ts) ts.
  Proof.
    unfold traces_match_abs; intros.
    inversion H2; clear H2; intuition idtac.
    edestruct x.compile_traces_match; intuition eauto.
      eapply y.compile_ts_no_atomics; eauto.
    edestruct y.compile_traces_match; intuition eauto.
  Qed.

End Link.


Module LinkWithRule
  (oA : Ops) (sA : State) (a : Layer oA sA)
  (oB : Ops) (sB : State) (b : Layer oB sB)
  (oC : Ops) (sC : State) (c : Layer oC sC)
  (r : ProcRule oB)
  (x : LayerImplRequiresRule oA sA a oB sB b r)
  (y : LayerImplFollowsRule oB sB b oC sC c r) <: LayerImpl oA sA a oC sC c.

  Definition absR (s1 : sA.State) (s3 : sC.State) :=
    exists s2, x.absR s1 s2 /\ y.absR s2 s3.

  Definition compile_ts ts :=
    x.compile_ts (y.compile_ts ts).

  Theorem compile_ts_no_atomics :
    forall ts,
      no_atomics_ts ts ->
      no_atomics_ts (compile_ts ts).
  Proof.
    intros.
    eapply x.compile_ts_no_atomics.
    eapply y.compile_ts_no_atomics.
    eauto.
  Qed.

  Theorem absInitP :
    forall s1 s2,
      sA.initP s1 ->
      absR s1 s2 ->
      sC.initP s2.
  Proof.
    unfold absR; intros; deex.
    eauto.
  Qed.

  Theorem compile_traces_match :
    forall ts,
      no_atomics_ts ts ->
      traces_match_abs absR sA.initP a.step c.step (compile_ts ts) ts.
  Proof.
    unfold traces_match_abs; intros.
    inversion H2; clear H2; intuition idtac.
    edestruct x.compile_traces_match; intuition eauto.
      eapply y.compile_ts_follows_protocol; eauto.
      eapply y.compile_ts_no_atomics; eauto.
    edestruct y.compile_traces_match; intuition eauto.
  Qed.

End LinkWithRule.
