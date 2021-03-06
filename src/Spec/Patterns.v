Require Import ConcurExec.
Require Import Equiv ProcMatch.
Require Import Compile.
Require Import Abstraction.
Require Import Movers.
Require Import Protocol.
Require Import CompileLoop.
Require Import ProofAutomation.

Require Import Helpers.Instances.

(** Combining trace matching with state abstraction. *)

Section TraceAbs.

  Variable OpLo : Type -> Type.
  Variable OpHi : Type -> Type.

  Variable StateLo : Type.
  Variable StateHi : Type.
  Variable absR : StateLo -> StateHi -> Prop.
  Variable initP : StateLo -> Prop.
  Variable initHi : StateHi -> Prop.

  Variable lo_step : OpSemantics OpLo StateLo.
  Variable hi_step : OpSemantics OpHi StateHi.

  (* TCB: this definition is the core of our specifications: we prove that all
  behaviors of threads using low-level operations are also behaviors that could
  be produced by the corresponding high-level code (our proofs will be for all
  ts2, relating them to a compiled version using low-level operations that we
  can actually execute) *)
  Definition traces_match_abs
                           (ts1 : threads_state OpLo)
                           (ts2 : threads_state OpHi) :=
    forall (sl : StateLo) tr1,
      initP sl ->
      exec lo_step sl ts1 tr1 ->
      exists sm, absR sl sm /\
            initHi sm /\
            exec hi_step sm ts2 tr1.

End TraceAbs.


Module Type Ops.

  Axiom Op : Type -> Type.

End Ops.


Module Type State.

  Axiom State : Type.

End State.


Module Type Layer (o : Ops) (s : State).

  Axiom step : OpSemantics o.Op s.State.
  Axiom initP : s.State -> Prop.

End Layer.


Module Type Protocol (o : Ops) (s : State).

  Axiom step_allow : forall T, o.Op T -> nat -> s.State -> Prop.

End Protocol.


Module Type LayerImpl
  (o1 : Ops) (s1 : State) (l1 : Layer o1 s1)
  (o2 : Ops) (s2 : State) (l2 : Layer o2 s2).

  Axiom absR : s1.State -> s2.State -> Prop.
  Axiom compile_ts : threads_state o2.Op -> threads_state o1.Op.
  Axiom compile_ts_no_atomics :
    forall ts,
      no_atomics_ts ts ->
      no_atomics_ts (compile_ts ts).
  Axiom absInitP :
    forall s1,
      l1.initP s1 ->
      exists s2, absR s1 s2 /\
      l2.initP s2.
  Axiom compile_traces_match :
    forall ts,
      no_atomics_ts ts ->
      traces_match_abs absR l1.initP l2.initP l1.step l2.step (compile_ts ts) ts.

  Hint Resolve absInitP.

End LayerImpl.


Module Type LayerImplAbsT
  (o : Ops)
  (s1 : State) (l1 : Layer o s1)
  (s2 : State) (l2 : Layer o s2).

  Axiom absR : s1.State -> s2.State -> Prop.
  Axiom absR_ok : op_abs absR l1.step l2.step.
  Axiom absInitP :
    forall s1, l1.initP s1 ->
          exists s2, absR s1 s2 /\ l2.initP s2.

End LayerImplAbsT.


Module LayerImplAbs
  (o : Ops)
  (s1 : State) (l1 : Layer o s1)
  (s2 : State) (l2 : Layer o s2)
  (a : LayerImplAbsT o s1 l1 s2 l2) <: LayerImpl o s1 l1 o s2 l2.

  Definition absR := a.absR.
  Definition absInitP := a.absInitP.

  Definition compile_ts (ts : threads_state o.Op) := ts.

  Theorem compile_ts_no_atomics :
    forall (ts : threads_state o.Op),
      no_atomics_ts ts ->
      no_atomics_ts (compile_ts ts).
  Proof.
    unfold compile_ts; eauto.
  Qed.

  Hint Resolve a.absR_ok.

  Theorem compile_traces_match :
    forall ts,
      no_atomics_ts ts ->
      traces_match_abs absR l1.initP l2.initP l1.step l2.step (compile_ts ts) ts.
  Proof.
    unfold compile_ts, traces_match_abs; intros.
    eapply absInitP in H0; propositional; eauto using trace_incl_abs.
  Qed.

End LayerImplAbs.


Module Type LayerImplMoversT
  (s : State)
  (o1 : Ops) (l1 : Layer o1 s)
  (o2 : Ops) (l2 : Layer o2 s).

  Axiom compile_op : forall T, o2.Op T -> proc o1.Op T.

  Axiom compile_op_no_atomics : forall T (op : o2.Op T),
    no_atomics (compile_op op).

  Axiom ysa_movers : forall T (op : o2.Op T),
    ysa_movers l1.step (compile_op op).

  Axiom compile_correct :
    compile_correct compile_op l1.step l2.step.

  Axiom initP_compat : forall s,
      l1.initP s -> l2.initP s.

End LayerImplMoversT.

Local Ltac init_abs :=
  repeat match goal with
         | [ |- forall _, _ ] => intros
         | [ |- exists s2, _ _ s2 /\ _ /\ _ ] =>
           eexists; split; [ reflexivity | split; [ now auto |  ] ]
         | |- exists s2, _ _ s2 /\ _ =>
           eexists; split; [ reflexivity | ]
         end.

Module LayerImplMovers
  (s : State)
  (o1 : Ops) (l1 : Layer o1 s)
  (o2 : Ops) (l2 : Layer o2 s)
  (a : LayerImplMoversT s o1 l1 o2 l2) <: LayerImpl o1 s l1 o2 s l2.

  Definition absR (s1 : s.State) (s2 : s.State) := s1 = s2.

  Theorem absInitP :
    forall s1,
      l1.initP s1 ->
      exists s2, absR s1 s2 /\
            l2.initP s2.
  Proof.
    init_abs; auto using a.initP_compat.
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

  Theorem op_atomic : forall `(op : o2.Op T) `(rx : _ -> proc _ R),
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
      traces_match_abs absR l1.initP l2.initP l1.step l2.step (compile_ts ts2) ts2.
  Proof.
    unfold traces_match_abs; intros.
    init_abs.
    intuition auto using a.initP_compat.
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

  Axiom op_follows_protocol : forall tid s `(op : o2.Op T),
    follows_protocol_proc l1raw.step p.step_allow tid s (compile_op op).

  Axiom allowed_stable :
    forall `(op : o1.Op T) `(op' : o1.Op T') tid tid' s s' r evs,
      tid <> tid' ->
      p.step_allow op tid s ->
      l1.step op' tid' s r s' evs ->
      p.step_allow op tid s'.

  (* This means that l1.step is either restricted_step or nilpotent_step *)
  Axiom raw_step_ok :
    forall `(op : o1.Op T) tid s r s' evs,
      restricted_step l1raw.step p.step_allow op tid s r s' evs ->
      l1.step op tid s r s' evs.

  Axiom raw_initP_compat :
    forall s, l1raw.initP s -> l1.initP s.

End LayerImplMoversProtocolT.


Module LayerImplMoversProtocol
  (s : State)
  (o1 : Ops) (l1raw : Layer o1 s) (l1 : Layer o1 s)
  (o2 : Ops) (l2 : Layer o2 s)
  (p : Protocol o1 s)
  (a : LayerImplMoversProtocolT s o1 l1raw l1 o2 l2 p) <: LayerImpl o1 s l1raw o2 s l2.

  Definition absR (s1 : s.State) (s2 : s.State) := s1 = s2.

  Theorem absInitP :
    forall s1,
      l1raw.initP s1 ->
      exists s2, absR s1 s2 /\
      l2.initP s2.
  Proof.
    unfold absR; init_abs; auto using a.initP_compat, a.raw_initP_compat.
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

  Theorem op_atomic : forall `(op : o2.Op T) `(rx : _ -> proc _ R),
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
      traces_match_abs absR l1.initP l2.initP l1.step l2.step (compile_ts ts2) ts2.
  Proof.
    unfold traces_match_abs; init_abs.
    intuition auto using a.initP_compat.
    eapply all_traces_match; eauto.
    eapply Compile.compile_ts_ok; eauto.
  Qed.

  Definition follows_protocol (ts : threads_state o1.Op) :=
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

  Lemma follows_protocol_s_spawn:
    forall (ts : threads_state _) (s : s.State) (T : Type) (tid tid' : nat)
      (p : proc o1.Op T) (s' : s.State) (evs : list event)
      (result : T + proc o1.Op T) (spawned : maybe_proc o1.Op),
      tid <> tid' ->
      ts tid' = NoProc ->
      follows_protocol_s l1raw.step p.step_allow ts s ->
      exec_tid l1raw.step tid s p s' result spawned evs ->
      follows_protocol_proc l1raw.step p.step_allow tid s p ->
      follows_protocol_s l1raw.step p.step_allow (ts [[tid' := spawned]]) s.
  Proof.
    intros.
    destruct spawned; cycle 1.
    rewrite thread_upd_same_eq with (tid:=tid') in * by auto; eauto.
    unfold follows_protocol_s; intros.
    cmp_ts tid0 tid'; repeat maybe_proc_inv; eauto.
    remember (Proc p1).
    generalize dependent p1.
    generalize dependent tid'.
    induction H2; propositional; eauto; NoProc_upd;
      repeat maybe_proc_inv.
    invert H3.
    eapply IHexec_tid; eauto.
    invert H3; eauto.
  Qed.

  Lemma no_atomics_ts_exec_spawn:
    forall (ts : threads_state _) (s : s.State),
      no_atomics_ts ts ->
      forall (T : Type) (tid tid' : nat) (p : proc o1.Op T) (s' : s.State)
        (evs : list event) (result : T + proc o1.Op T) (T0 : Type)
        (p0 : proc o1.Op T0),
        ts tid = Proc p ->
        exec_tid l1raw.step tid s p s' result (Proc p0) evs ->
        no_atomics_ts (ts [[tid' := Proc p0]]).
  Proof.
    intros.
    eapply no_atomics_thread_upd_Proc; auto.
    assert (no_atomics p).
    unfold no_atomics_ts in H0.
    eapply thread_Forall_some with (a:=tid) in H0; eauto.
    clear dependent ts.

    (* goal is now simplified to just be about one process *)
    remember (Proc p0).
    generalize dependent p0.
    induction H1; intros; repeat maybe_proc_inv; propositional.
    invert H2; eauto.
    invert H2.
  Qed.

  Theorem compile_traces_match_l1raw :
    forall ts,
      follows_protocol ts ->
      no_atomics_ts ts ->
      traces_match_abs absR l1raw.initP l1.initP l1raw.step l1.step ts ts.
  Proof.
    unfold compile_ts, follows_protocol, absR.
    unfold traces_match_abs; intros; subst.
    init_abs.
    intuition auto using a.raw_initP_compat.
    clear H1.
    specialize (H sl).
    induction H2; eauto.
    cmp_ts tid tid'.
    pose proof (H tid _ p ltac:(eauto)) as Htid.

    prove_hyps IHexec.
    - eapply follows_protocol_s_exec_tid_upd; eauto.
      intros; eapply a.allowed_stable; eauto.
      eapply a.raw_step_ok; eauto.

      destruct spawned.
      eauto using follows_protocol_s_spawn.
      rewrite thread_upd_same_eq with (tid:=tid') in * by auto; eauto.

      autorewrite with t; auto.

      destruct spawned; eauto using no_atomics_ts_exec_spawn,
                        no_atomics_thread_upd_NoProc.
    - destruct spawned.
      destruct matches; eauto using no_atomics_ts_exec_spawn.
      rewrite thread_upd_same_eq with (tid:=tid') in * by auto;
        destruct matches;
        eauto.
    - ExecPrefix tid tid'.
      eapply exec_tid_step_impl.
      intros; apply a.raw_step_ok; eauto.
      eapply follows_protocol_preserves_exec_tid'; eauto.
  Qed.

  Hint Resolve (_:Reflexive absR).
  Local Hint Resolve (_:Transitive absR).

  Local Hint Resolve compile_ts_no_atomics.
  Local Hint Resolve compile_ts_follows_protocol.
  Local Hint Resolve a.compile_op_no_atomics.

  Theorem compile_traces_match :
    forall ts,
      no_atomics_ts ts ->
      traces_match_abs absR l1raw.initP l2.initP l1raw.step l2.step (compile_ts ts) ts.
  Proof.
    unfold traces_match_abs; intros.
    eapply compile_traces_match_l1raw in H1; propositional; eauto.
    eapply compile_traces_match_l1 in H3; propositional; eauto.
  Qed.

  Theorem initP_compat : forall s,
      l1raw.initP s -> l2.initP s.
  Proof.
    auto using a.initP_compat, a.raw_initP_compat.
  Qed.

End LayerImplMoversProtocol.


Module Type LayerImplLoopT
  (s : State)
  (o1 : Ops) (l1 : Layer o1 s)
  (o2 : Ops) (l2 : Layer o2 s).

  Axiom compile_op : forall T, o2.Op T -> (option T -> o1.Op T) * (T -> bool) * option T.
  Axiom noop_or_success :
    noop_or_success compile_op l1.step l2.step.

  Axiom initP_compat :
    forall s, l1.initP s -> l2.initP s.

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
    forall s1,
      l1.initP s1 ->
      exists s2, absR s1 s2 /\
      l2.initP s2.
  Proof.
    unfold absR; eauto using a.initP_compat.
  Qed.

  Theorem compile_traces_match :
    forall ts,
      no_atomics_ts ts ->
      traces_match_abs absR l1.initP l2.initP l1.step l2.step (compile_ts ts) ts.
  Proof.
    unfold traces_match_abs, absR; intros; subst.
    init_abs.
    intuition auto using a.initP_compat.
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
    forall s1,
      a.initP s1 ->
      exists s2, absR s1 s2 /\ c.initP s2.
  Proof.
    unfold absR; intros.
    eapply x.absInitP in H; propositional.
    eapply y.absInitP in H0; propositional.
    eauto.
  Qed.

  Hint Resolve x.compile_ts_no_atomics y.compile_ts_no_atomics.

  Lemma absR_transitive : forall s1 s2 s3,
      x.absR s1 s2 ->
      y.absR s2 s3 ->
      absR s1 s3.
  Proof.
    unfold absR; eauto.
  Qed.

  Hint Resolve absR_transitive.

  Theorem compile_traces_match :
    forall ts,
      no_atomics_ts ts ->
      traces_match_abs absR a.initP c.initP a.step c.step (compile_ts ts) ts.
  Proof.
    unfold traces_match_abs; intros.
    eapply x.compile_traces_match in H1; propositional; eauto.
    eapply y.compile_traces_match in H3; propositional; eauto.
  Qed.

End Link.
