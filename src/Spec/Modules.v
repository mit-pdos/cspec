Require Import ConcurProc.
Require Import Equiv.
Require Import Compile.
Require Import Abstraction.


(** Combining trace matching with state abstraction. *)

Section TraceAbs.

  Variable opLoT : Type -> Type.
  Variable opMidT : Type -> Type.

  Variable StateLo : Type.
  Variable StateMid : Type.
  Variable absR : StateLo -> StateMid -> Prop.

  Variable lo_step : OpSemantics opLoT StateLo.
  Variable mid_step : OpSemantics opMidT StateMid.

  Definition traces_match_abs
                           (ts1 : @threads_state opLoT)
                           (ts2 : @threads_state opMidT) :=
  forall (sl : StateLo) (sm : StateMid) tr1,
    exec_prefix lo_step sl ts1 tr1 ->
    absR sl sm ->
    exists tr2,
      exec_prefix mid_step sm ts2 tr2 /\
      trace_eq tr1 tr2.

End TraceAbs.


Module Type Layer.

  Axiom opT : Type -> Type.
  Axiom State : Type.
  Axiom step : OpSemantics opT State.

End Layer.


Module Type ProcRule (l : Layer).

  Axiom follows_protocol : @threads_state l.opT -> Prop.

End ProcRule.


Module Type LayerImpl (l1 : Layer) (l2 : Layer).

  Axiom absR : l1.State -> l2.State -> Prop.
  Axiom compile_ts : @threads_state l2.opT -> @threads_state l1.opT.
  Axiom compile_ts_no_atomics :
    forall ts,
      no_atomics_ts ts ->
      no_atomics_ts (compile_ts ts).
  Axiom compile_traces_match :
    forall ts,
      no_atomics_ts ts ->
      traces_match_abs absR l1.step l2.step (compile_ts ts) ts.

End LayerImpl.


Module Type LayerImplRequiresRule (l1 : Layer) (l2 : Layer) (r : ProcRule l2).

  Axiom absR : l1.State -> l2.State -> Prop.
  Axiom compile_ts : @threads_state l2.opT -> @threads_state l1.opT.
  Axiom compile_ts_no_atomics :
    forall ts,
      no_atomics_ts ts ->
      no_atomics_ts (compile_ts ts).
  Axiom compile_traces_match :
    forall ts,
      r.follows_protocol ts ->
      no_atomics_ts ts ->
      traces_match_abs absR l1.step l2.step (compile_ts ts) ts.

End LayerImplRequiresRule.


Module Type LayerImplFollowsRule (l1 : Layer) (l2 : Layer) (r : ProcRule l1).

  Axiom absR : l1.State -> l2.State -> Prop.
  Axiom compile_ts : @threads_state l2.opT -> @threads_state l1.opT.
  Axiom compile_ts_no_atomics :
    forall ts,
      no_atomics_ts ts ->
      no_atomics_ts (compile_ts ts).
  Axiom compile_ts_follows_protocol :
    forall ts,
      no_atomics_ts ts ->
      r.follows_protocol (compile_ts ts).
  Axiom compile_traces_match :
    forall ts,
      no_atomics_ts ts ->
      traces_match_abs absR l1.step l2.step (compile_ts ts) ts.

End LayerImplFollowsRule.


(** General layer transformers. *)

Module Link
  (a : Layer) (b : Layer) (c : Layer)
  (x : LayerImpl a b) (y : LayerImpl b c) <: LayerImpl a c.

  Definition absR (s1 : a.State) (s3 : c.State) :=
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

  Theorem compile_traces_match :
    forall ts,
      no_atomics_ts ts ->
      traces_match_abs absR a.step c.step (compile_ts ts) ts.
  Proof.
    unfold traces_match_abs; intros.
    inversion H1; clear H1; intuition idtac.
    edestruct x.compile_traces_match; intuition eauto.
      eapply y.compile_ts_no_atomics; eauto.
    edestruct y.compile_traces_match; intuition eauto.
    eexists; intuition eauto.
    etransitivity; eauto.
  Qed.

End Link.


Module LinkWithRule
  (a : Layer) (b : Layer) (c : Layer) (r : ProcRule b)
  (x : LayerImplRequiresRule a b r) (y : LayerImplFollowsRule b c r) <: LayerImpl a c.

  Definition absR (s1 : a.State) (s3 : c.State) :=
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

  Theorem compile_traces_match :
    forall ts,
      no_atomics_ts ts ->
      traces_match_abs absR a.step c.step (compile_ts ts) ts.
  Proof.
    unfold traces_match_abs; intros.
    inversion H1; clear H1; intuition idtac.
    edestruct x.compile_traces_match; intuition eauto.
      eapply y.compile_ts_follows_protocol; eauto.
      eapply y.compile_ts_no_atomics; eauto.
    edestruct y.compile_traces_match; intuition eauto.
    eexists; intuition eauto.
    etransitivity; eauto.
  Qed.

End LinkWithRule.
