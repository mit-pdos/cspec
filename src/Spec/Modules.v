Require Import ConcurProc.
Require Import Equiv.
Require Import Compile.
Require Import Abstraction.


(** Combining trace matching with state abstraction. *)

Section TraceAbs.

  Variable opLoT : Type -> Type.
  Variable opMidT : Type -> Type.
  Variable opHiT : Type -> Type.

  Variable StateLo : Type.
  Variable StateMid : Type.
  Variable absR : StateLo -> StateMid -> Prop.

  Variable lo_step : OpSemantics opLoT StateLo.
  Variable mid_step : OpSemantics opMidT StateMid.

  Definition traces_match_abs
                           (ts1 : @threads_state opLoT opHiT)
                           (ts2 : @threads_state opMidT opHiT) :=
  forall (sl : StateLo) (sm : StateMid) tr1,
    exec_prefix lo_step sl ts1 tr1 ->
    absR sl sm ->
    exists tr2,
      exec_prefix mid_step sm ts2 tr2 /\
      trace_match_hi tr1 tr2.

End TraceAbs.


Module Type Layer.

  Axiom opT : Type -> Type.
  Axiom State : Type.
  Axiom step : OpSemantics opT State.

End Layer.


Module Type LayerImpl (l1 : Layer) (l2 : Layer).

  Axiom absR : l1.State -> l2.State -> Prop.
  Axiom compile_ts :
    forall l3opT, @threads_state l2.opT l3opT -> @threads_state l1.opT l3opT.
  Axiom compile_traces_match :
    forall `(ts2 : @threads_state _ l3opT),
      traces_match_abs absR l1.step l2.step (compile_ts ts2) ts2.

End LayerImpl.
