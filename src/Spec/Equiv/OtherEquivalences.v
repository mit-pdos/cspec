Require Import Spec.ConcurExec.
Require Import Spec.ThreadsState.
Require Import Spec.Equiv.Execution.

Require Import ProofAutomation.
Require Import Spec.Equiv.Automation.
Require Import Helpers.Instances.

Require Import Relations.Relation_Operators.
Require Import Morphisms.
Require Import List.
Require Import Omega.

Global Set Implicit Arguments.
Global Generalizable All Variables.

Section OpSemantics.

  Context {Op:Type -> Type}.
  Context {State:Type}.
  Variable op_step: OpSemantics Op State.

  Local Obligation Tactic := try RelInstance_t.

  (** Trace inclusion for an entire threads_state *)

  Definition trace_incl_ts_s s (ts1 ts2 : threads_state Op) :=
    forall tr,
      exec op_step s ts1 tr ->
      exec op_step s ts2 tr.

  Definition trace_incl_ts (ts1 ts2 : threads_state Op) :=
    forall tr (s : State),
      exec op_step s ts1 tr ->
      exec op_step s ts2 tr.

  Global Program Instance trace_incl_ts_preorder :
    PreOrder trace_incl_ts.
  Next Obligation.
    hnf; intros.
    eauto.
  Qed.
  Next Obligation.
    unfold trace_incl_ts in *; eauto.
  Qed.

  Global Instance exec_equiv_ts_to_trace_incl_ts :
    subrelation (exec_equiv_ts op_step) trace_incl_ts.
  Proof.
    unfold subrelation; intros.
    unfold trace_incl_ts; intros.
    apply H in H0.
    eauto.
  Qed.

  (** Trace inclusion for a single thread *)

  Definition trace_incl_s `(s : State) tid `(p1 : proc Op T) (p2 : proc _ T) :=
    forall ts,
      trace_incl_ts_s s
                      (ts [[ tid := Proc p1 ]])
                      (ts [[ tid := Proc p2 ]]).

  Definition trace_incl {T} (p1 p2 : proc Op T) :=
    forall (ts : threads_state Op) tid,
      trace_incl_ts
        (ts [[ tid := Proc p1 ]])
        (ts [[ tid := Proc p2 ]]).

  (* natural definition of trace_incl_rx, defined in terms of all executions
     (that is, without requiring counters be identical) *)
  Definition trace_incl_rx' {T} (p1 p2 : proc Op T) :=
    forall TF (rx1 rx2: _ -> proc _ TF),
      (forall a, trace_incl (rx1 a) (rx2 a)) ->
      trace_incl (Bind p1 rx1) (Bind p2 rx2).

  Hint Constructors exec_tid.
  Hint Constructors exec_till.

  Theorem trace_incl_trace_incl_s : forall T (p1 p2 : proc Op T),
      trace_incl p1 p2 <->
      (forall s tid,
          trace_incl_s s tid p1 p2).
  Proof.
    unfold trace_incl, trace_incl_s, trace_incl_ts, trace_incl_ts_s.
    split; eauto.
  Qed.

  Ltac forward_chaining :=
    repeat (hnf; intros);
    repeat match goal with
           | [ H: _ |- _ ] => apply H
           end.

  Local Obligation Tactic := try solve [ forward_chaining ].

  Global Program Instance trace_incl_s_preorder :
    PreOrder (@trace_incl_s s tid T).

  Global Program Instance trace_incl_preorder :
    PreOrder (@trace_incl T).

  Global Program Instance exec_equiv_to_trace_incl :
    subrelation (exec_equiv op_step (T:=T)) (@trace_incl T).

  Global Program Instance trace_incl_proper :
    Proper (Basics.flip (@trace_incl T) ==>
                        @trace_incl T ==>
                        Basics.impl) (@trace_incl T).

  Global Program Instance trace_incl_proper_flip :
    Proper (@trace_incl T ==>
                        Basics.flip (@trace_incl T) ==>
                        Basics.flip Basics.impl) (@trace_incl T).

  Global Program Instance trace_incl_s_proper :
    Proper (Basics.flip (@trace_incl T) ==>
                        @trace_incl T ==>
                        Basics.impl) (@trace_incl_s s tid T).

  Global Program Instance trace_incl_s_proper_flip :
    Proper (@trace_incl T ==>
                        Basics.flip (@trace_incl T) ==>
                        Basics.flip Basics.impl) (@trace_incl_s s tid T).

  Global Program Instance trace_incl_s_exec_equiv_proper :
    Proper (exec_equiv op_step ==> exec_equiv op_step ==> iff)
           (@trace_incl_s s tid T).
  Next Obligation.
    split; forward_chaining.
  Qed.

  Global Program Instance trace_incl_exec_equiv_proper :
    Proper (exec_equiv op_step ==> exec_equiv op_step ==> iff)
           (@trace_incl T).
  Next Obligation.
    split; forward_chaining.
  Qed.

  Local Lemma trace_incl_ts_s_proof_helper :
    forall `(p1 : proc Op T) (p2 : proc _ T) ts tid s,
      (forall (ts: threads_state _) tid' s0 s' result tr spawned evs,
          exec_others op_step tid s s0 ->
          ts tid' = NoProc ->
          tid <> tid' ->
          exec_tid op_step tid s0 p1 s' result spawned evs ->
          exec op_step s' (ts [[tid' := spawned]] [[tid := match result with
                                                           | inl _ => NoProc
                                                           | inr p' => Proc p'
                                                           end]]) tr ->
          exec op_step s0 (ts [[tid := Proc p2]]) (prepend tid evs tr)) ->
      trace_incl_ts_s s
                      (ts [[ tid := Proc p1 ]])
                      (ts [[ tid := Proc p2 ]]).
  Proof.
    unfold trace_incl_ts_s.
    intros.
    ExecEquiv tt.
    ExecPrefix tid0 tid'.
    abstract_ts.
    eapply IHexec; intros; eauto with exec.
    auto with nocore exec.

    Grab Existential Variables.
    all: exact (Ret tt).
  Qed.

  Lemma trace_incl_proof_helper :
    forall `(p1 : proc Op T) p2,
      (forall tid tid' (ts: threads_state _) s s' result tr spawned evs,
          exec_tid op_step tid s p1 s' result spawned evs ->
          ts tid' = NoProc ->
          tid <> tid' ->
          exec op_step s' (ts [[tid' := spawned]] [[tid := match result with
                                                           | inl _ => NoProc
                                                           | inr p' => Proc p'
                                                           end]]) tr ->
          exec op_step s (ts [[tid := Proc p2]]) (prepend tid evs tr)) ->
      trace_incl p1 p2.
  Proof.
    unfold trace_incl, trace_incl_ts.
    intros.

    eapply trace_incl_ts_s_proof_helper; eauto.
  Qed.

  Lemma trace_incl_s_proof_helper :
    forall `(p1 : proc Op T) p2 s tid,
      (forall (ts: threads_state _) tid' s0 s' result tr spawned evs,
          exec_others op_step tid s s0 ->
          ts tid' = NoProc ->
          tid <> tid' ->
          exec_tid op_step tid s0 p1 s' result spawned evs ->
          exec op_step s' (ts [[tid' := spawned]] [[tid := match result with
                                                           | inl _ => NoProc
                                                           | inr p' => Proc p'
                                                           end]]) tr ->
          exists tr',
            exec op_step s0 (ts [[tid := Proc p2]]) tr' /\
            prepend tid evs tr = tr') ->
      trace_incl_s s tid p1 p2.
  Proof.
    unfold trace_incl_s.
    intros.

    eapply trace_incl_ts_s_proof_helper.
    intros.
    eapply H in H2; eauto.
    propositional.
  Qed.

  Theorem trace_incl_op :
    forall `(p : T -> proc Op T') op,
      trace_incl
                 (Bind (Call op) p)
                 (Bind (Atomic (Call op)) p).
  Proof.
    intros.
    eapply trace_incl_proof_helper; intros.
    repeat exec_tid_inv.

    ExecPrefix tid tid'.
  Qed.

  Theorem trace_incl_bind_a : forall `(p : proc Op T) `(p2 : T -> proc _ T') p2',
      (forall x, trace_incl (p2 x) (p2' x)) ->
      trace_incl (Bind p p2) (Bind p p2').
  Proof.
    unfold trace_incl, trace_incl_ts, trace_incl_ts_s.
    intros.

    ExecEquiv p.
    destruct result0; guess_ExecPrefix.
  Qed.

  Theorem trace_incl_s_bind_a : forall `(p : proc Op T) `(p2 : T -> proc _ T') p2' s tid,
      (forall s' x,
          exec_any op_step tid s p x s' ->
          trace_incl_s s' tid (p2 x) (p2' x)) ->
      trace_incl_s s tid (Bind p p2) (Bind p p2').
  Proof.
    unfold trace_incl_s, trace_incl_ts_s.
    intros.

    thread_upd_ind p.

    cmp_ts tid0 tid.
    + repeat maybe_proc_inv.
      exec_tid_inv.
      destruct result0.

      * ExecPrefix tid tid'.
        eauto.
      * ExecPrefix tid tid'.
        eauto.

    + ExecPrefix tid0 tid'.
      abstract_ts.
      eapply IHexec; intros; eauto with exec.
      eauto with exec.
  Qed.

  Global Instance Bind_trace_incl_proper_2 :
    Proper (eq ==> pointwise_relation T0 (@trace_incl T) ==>
               @trace_incl T) Bind.
  Proof.
    intros.
    intros p1a p1b H1; subst.
    intros p2a p2b H2.
    eapply trace_incl_bind_a; intros.
    eapply H2.
  Qed.

End OpSemantics.

(** Correspondence between different layers *)

Definition traces_match_ts {OpLo OpHi State} lo_step hi_step
           (ts1 : threads_state OpLo)
           (ts2 : threads_state OpHi) :=
  forall (s : State) tr1,
    exec lo_step s ts1 tr1 ->
    exec hi_step s ts2 tr1.

Global Instance traces_match_ts_proper :
  Proper (@trace_incl_ts OpLo State lo_step ==>
                         @exec_equiv_ts OpHi State hi_step ==>
                         Basics.flip Basics.impl)
         (@traces_match_ts OpLo OpHi State lo_step hi_step).
Proof.
  repeat (hnf; intros).
  repeat match goal with
         | [ H: _ |- _ ] => apply H
         end.
Qed.
