Require Import ConcurProc.
Require Import Relations.Relation_Operators.
Require Import RelationClasses.
Require Import Morphisms.
Require Import Helpers.Helpers.

Global Set Implicit Arguments.
Global Generalizable All Variables.


(** Matching traces *)

Inductive traces_match {opLoT opMidT opHiT} :
  forall (t1 : trace opLoT opMidT)
         (t2 : trace opMidT opHiT), Prop :=

| MatchLo : forall t1 t2 tid e,
  traces_match t1 t2 ->
  traces_match (TraceEvent tid (EvLow e) t1) t2

| MatchInvokeMid : forall t1 t2 tid e,
  traces_match t1 t2 ->
  traces_match (TraceEvent tid (EvHigh e) t1)
               (TraceEvent tid (EvLow e) t2)

| MatchInvokeHi : forall t1 t2 tid e,
  traces_match t1 t2 ->
  traces_match t1 (TraceEvent tid (EvHigh e) t2)

| MatchEmpty :
  traces_match TraceEmpty TraceEmpty.

Hint Constructors traces_match.


Fixpoint trace_filter_hi `(t : trace opLoT opHiT) : trace opLoT opHiT :=
  match t with
  | TraceEmpty => TraceEmpty
  | TraceEvent tid e t' =>
    match e with
    | EvLow _ => trace_filter_hi t'
    | EvHigh _ => TraceEvent tid e (trace_filter_hi t')
    end
  end.

Definition trace_match_hi {opLoT opHiT} (t1 t2 : trace opLoT opHiT) :=
  trace_filter_hi t1 = trace_filter_hi t2.

Instance trace_match_hi_preorder {opLoT opHiT} :
  PreOrder `(@trace_match_hi opLoT opHiT).
Proof.
  split.
  - firstorder.
  - unfold trace_match_hi, Transitive; intros.
    congruence.
Qed.

Lemma trace_match_hi_prepend : forall `(evs : list (event opT opHiT)) tr0 tr1 tid,
  trace_match_hi tr0 tr1 ->
  trace_match_hi (prepend tid evs tr0) (prepend tid evs tr1).
Proof.
  unfold trace_match_hi.
  induction evs; simpl; intros; eauto.
  destruct a; eauto.
  erewrite IHevs; eauto.
Qed.

Hint Resolve trace_match_hi_prepend.


Lemma trace_match_hi_drop_lo_l : forall opT opHiT e (tr1 tr2 : trace opT opHiT) tid,
  trace_match_hi tr1 tr2 ->
  trace_match_hi (TraceEvent tid (EvLow e) tr1) tr2.
Proof.
  unfold trace_match_hi; simpl; eauto.
Qed.

Lemma trace_match_hi_drop_lo_r : forall opLoT opHiT e (tr1 tr2 : trace opLoT opHiT) tid,
  trace_match_hi tr1 tr2 ->
  trace_match_hi tr1 (TraceEvent tid (EvLow e) tr2).
Proof.
  unfold trace_match_hi; simpl; eauto.
Qed.

Hint Resolve trace_match_hi_drop_lo_l.
Hint Resolve trace_match_hi_drop_lo_r.


(** Preserving traces for an entire threads_state *)

Definition same_traces_s {opLo opHi State} op_step (s s' : State) (ts1 ts2 : @threads_state opLo opHi) :=
  forall tr,
    exec op_step s ts1 tr ->
    exists tr', exec op_step s' ts2 tr' /\
      trace_match_hi tr tr'.

Definition same_traces {opLo opHi State} op_step (s : State) (ts1 ts2 : @threads_state opLo opHi) :=
  same_traces_s op_step s s ts1 ts2.


Instance same_traces_preorder {opT opHiT State op_step s} :
  PreOrder (@same_traces opT opHiT State op_step s).
Proof.
  split.
  - unfold Reflexive.
    unfold same_traces, same_traces_s; intros.
    eexists; intuition eauto.
    reflexivity.
  - unfold Transitive.
    unfold same_traces, same_traces_s; intros.
    eapply H in H1. deex.
    eapply H0 in H1. deex.
    eexists; intuition eauto.
    etransitivity; eauto.
Qed.


(** A strong notion of execution equivalence, independent of semantics *)

Definition exec_equiv_ts {opT opHiT} (ts1 ts2 : @threads_state opT opHiT) :=
  forall State op_step (s : State) tr,
    exec op_step s ts1 tr <->
    exec op_step s ts2 tr.

Definition exec_equiv_opt `(p1 : maybe_proc opT opHiT) p2 :=
  forall (ts : threads_state) tid,
    exec_equiv_ts (ts [[ tid := p1 ]]) (ts [[ tid := p2 ]]).

Definition exec_equiv `(p1 : proc opT opHiT T) (p2 : proc _ _ T) :=
  exec_equiv_opt (Proc p1) (Proc p2).

Instance exec_equiv_ts_preorder {opLoT opHiT} :
  PreOrder (@exec_equiv_ts opLoT opHiT).
Proof.
  split.
  - firstorder.
  - unfold Transitive, exec_equiv_ts; intros.
    split; intros.
    + apply H0. apply H. eauto.
    + apply H. apply H0. eauto.
Qed.


(** Preserving traces for a single thread *)

Definition trace_equiv_s `(s : State) s' tid `(op_step : OpSemantics opT State) `(p1 : proc opT opHiT T) (p2 : proc _ _ T) :=
  forall ts,
    same_traces_s op_step s s'
      (ts [[ tid := Proc p1 ]])
      (ts [[ tid := Proc p2 ]]).

Definition trace_equiv {opT opHiT T} `(op_step : OpSemantics opT State) (p1 p2 : proc opT opHiT T) :=
  forall ts s tid,
    same_traces op_step s
      (ts [[ tid := Proc p1 ]])
      (ts [[ tid := Proc p2 ]]).


Instance trace_equiv_preorder {opT opHiT T State op_step} :
  PreOrder (@trace_equiv opT opHiT T State op_step).
Proof.
  split.
  - unfold Reflexive; intros.
    unfold trace_equiv; intros.
    reflexivity.
  - unfold Transitive; intros.
    unfold trace_equiv; intros.
    etransitivity; eauto.
Qed.

Instance trace_equiv_proper {opT opHiT T State op_step} :
  Proper (Basics.flip (@trace_equiv opT opHiT T State op_step) ==>
          @trace_equiv opT opHiT T State op_step ==>
          Basics.impl) (@trace_equiv opT opHiT T State op_step).
Proof.
  intros p1 p2 H21 p3 p4 H34 H; subst.
  unfold Basics.flip in *.
  repeat (etransitivity; eauto).
Qed.

Instance trace_equiv_proper_flip {opT opHiT T State op_step} :
  Proper (@trace_equiv opT opHiT T State op_step ==>
          Basics.flip (@trace_equiv opT opHiT T State op_step) ==>
          Basics.flip Basics.impl) (@trace_equiv opT opHiT T State op_step).
Proof.
  intros p1 p2 H21 p3 p4 H34 H; subst.
  unfold Basics.flip in *.
  repeat (etransitivity; eauto).
Qed.
