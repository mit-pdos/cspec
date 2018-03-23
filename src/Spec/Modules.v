Require Import ConcurProc.
Require Import Equiv.
Require Import Compile.
Require Import Abstraction.
Require Import Movers.
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
      exists tr2,
        exec_prefix mid_step sm ts2 tr2 /\
        trace_eq tr1 tr2.

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

  Axiom absR : s1.State -> s2.State -> Prop.
  Axiom compile_ts : @threads_state o2.opT -> @threads_state o1.opT.
  Axiom compile_ts_no_atomics :
    forall ts,
      no_atomics_ts ts ->
      no_atomics_ts (compile_ts ts).
  Axiom compile_ts_follows_protocol :
    forall ts,
      no_atomics_ts ts ->
      r.follows_protocol (compile_ts ts).
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
    eexists; intuition idtac.
    eapply trace_incl_abs; eauto.
    eauto.
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
    eexists; intuition eauto.
    etransitivity; eauto.
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
    eexists; intuition eauto.
    etransitivity; eauto.
  Qed.

End LinkWithRule.
