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

Module Layer.
  Section S.
    Record t Op State : Type :=
      { step : OpSemantics Op State;
        initP : State -> Prop; }.
  End S.
End Layer.

Module Protocol.
  Section S.
    Record t (Op: Type -> Type) State :=
      { step_allow : forall T, Op T -> nat -> State -> Prop; }.
  End S.
End Protocol.

Module LayerImpl.
  Import Layer.
  Section S.
    Context
      `(l1 : Layer.t O1 S1)
      `(l2 : Layer.t O2 S2).

    Record t :=
      { absR : S1 -> S2 -> Prop;
        compile_ts : threads_state O2 -> threads_state O1;
        compile_ts_no_atomics :
          forall ts,
            no_atomics_ts ts ->
            no_atomics_ts (compile_ts ts);
        absInitP :
          forall s1,
            l1.(initP) s1 ->
            exists s2, absR s1 s2 /\
                       l2.(initP) s2;
        compile_traces_match :
          forall ts,
            no_atomics_ts ts ->
            traces_match_abs absR l1.(initP) l2.(initP) l1.(step) l2.(step) (compile_ts ts) ts; }.

  End S.
End LayerImpl.

Module LayerImplAbsT.
  Import Layer.
  Section S.
    Context O
            `(l1: Layer.t O S1)
            `(l2: Layer.t O S2).

    Record t :=
      { absR : S1 -> S2 -> Prop;
        absR_ok : op_abs absR l1.(step) l2.(step);
        absInitP :
          forall s1, l1.(initP) s1 ->
                     exists s2, absR s1 s2 /\ l2.(initP) s2; }.
  End S.

End LayerImplAbsT.


Module LayerImplAbs.
  Import Layer.
  Import LayerImplAbsT.
  Section S.
    Context O
            `(l1 : Layer.t O S1)
            `(l2 : Layer.t O S2)
            (a : LayerImplAbsT.t l1 l2).

    Definition absR := a.(absR).
    Definition absInitP := a.(absInitP).

    Definition compile_ts (ts : threads_state O) := ts.

    Theorem compile_ts_no_atomics :
      forall (ts : threads_state O),
        no_atomics_ts ts ->
        no_atomics_ts (compile_ts ts).
    Proof.
      unfold compile_ts; eauto.
    Qed.

    Hint Resolve absR_ok.

    Theorem compile_traces_match :
      forall ts,
        no_atomics_ts ts ->
        traces_match_abs absR l1.(initP) l2.(initP) l1.(step) l2.(step) (compile_ts ts) ts.
    Proof.
      unfold compile_ts, traces_match_abs; intros.
      eapply absInitP in H0; propositional; eauto using trace_incl_abs.
    Qed.

    Definition t : LayerImpl.t l1 l2.
      refine {| LayerImpl.absR := absR;
                LayerImpl.absInitP := absInitP;
                LayerImpl.compile_ts := compile_ts;
                LayerImpl.compile_ts_no_atomics := compile_ts_no_atomics;
                LayerImpl.compile_traces_match := compile_traces_match; |}.
    Defined.

  End S.

End LayerImplAbs.

Module LayerImplMoversT.
  Import Layer.
  Section S.
    Context S
            `(l1: Layer.t O1 S)
            `(l2: Layer.t O2 S).
    Record t :=
      { compile_op : forall T, O2 T -> proc O1 T;
        compile_op_no_atomics : forall T (op : O2 T),
            no_atomics (compile_op op);
        ysa_movers : forall T (op : O2 T), ysa_movers l1.(step) (compile_op op);
        compile_correct : compile_correct compile_op l1.(step) l2.(step);
        initP_compat : forall s, l1.(initP) s -> l2.(initP) s;
      }.

  End S.
  Arguments compile_op [S] {O1} [l1] {O2} [l2] _ [T] op.
End LayerImplMoversT.

Local Ltac init_abs :=
  repeat match goal with
         | [ |- forall _, _ ] => intros
         | [ |- exists s2, _ _ s2 /\ _ /\ _ ] =>
           eexists; split; [ reflexivity | split; [ now auto |  ] ]
         | |- exists s2, _ _ s2 /\ _ =>
           eexists; split; [ reflexivity | ]
         end.


Module LayerImplMovers.
  Import Layer.
  Import LayerImplMoversT.
  Section S.
    Context S
            `(l1 : Layer.t O1 S)
            `(l2 : Layer.t O2 S)
            (a : LayerImplMoversT.t l1 l2).

    Definition absR (s1 : S) (s2: S) := s1 = s2.
    
    Theorem absInitP :
      forall s1,
        l1.(initP) s1 ->
        exists s2, absR s1 s2 /\
                   l2.(initP) s2.
    Proof.
      init_abs; auto using a.(initP_compat).
    Qed.

    Definition compile_ts := Compile.compile_ts a.(compile_op).

    Theorem compile_ts_no_atomics :
      forall ts,
        no_atomics_ts ts ->
        no_atomics_ts (compile_ts ts).
    Proof.
      eapply Compile.compile_ts_no_atomics.
      eapply a.(compile_op_no_atomics).
    Qed.

    Check a.(compile_op).

    Theorem op_atomic : forall T (op : O2 T) `(rx : _ -> proc _ R),
        trace_incl l1.(step)
                        (Bind (a.(compile_op) op) rx)
                        (Bind (atomize a.(compile_op) op) rx).
    Proof.
      intros.
      eapply trace_incl_atomize_ysa.
      eapply a.(ysa_movers).
    Qed.

    Theorem atomize_correct :
      atomize_correct a.(compile_op) l1.(step).
    Proof.
      unfold atomize_correct; intros.
      rewrite op_atomic.
      eapply trace_incl_bind_a.
      eauto.
    Qed.

    Hint Resolve atomize_correct.

    Theorem all_traces_match :
      forall ts1 ts2,
        proc_match (Compile.compile_ok a.(compile_op)) ts1 ts2 ->
        traces_match_ts l1.(step) l2.(step) ts1 ts2.
    Proof.
      intros.
      eapply Compile.compile_traces_match_ts; eauto.
      eapply a.(compile_correct).
    Qed.

    Theorem compile_traces_match :
      forall ts2,
        no_atomics_ts ts2 ->
        traces_match_abs absR l1.(initP) l2.(initP) l1.(step) l2.(step) (compile_ts ts2) ts2.
    Proof.
      unfold traces_match_abs; intros.
      init_abs.
      intuition auto using a.(initP_compat).
      eapply all_traces_match; eauto.
      eapply Compile.compile_ts_ok; eauto.
    Qed.

    Definition t : LayerImpl.t l1 l2.
      refine {| LayerImpl.absR := absR;
                LayerImpl.compile_ts := compile_ts;
                LayerImpl.compile_ts_no_atomics := compile_ts_no_atomics;
                LayerImpl.absInitP := absInitP;
                LayerImpl.compile_traces_match := compile_traces_match;
             |}.
    Defined.
  End S.
End LayerImplMovers.

Module LayerImplMoversProtocolT.
  Import Layer.
  Import LayerImplMoversT.
  Import Protocol.
  Section S.
    Context S
            `(l1raw: Layer.t O1 S) (l1: Layer.t O1 S)
            `(l2: Layer.t O2 S)
            (p: Protocol.t O1 S).

    Record t : Type :=
      { movers_impl :> LayerImplMoversT.t l1 l2;
        op_follows_protocol : forall tid S T (op : O2 T),
            follows_protocol_proc l1raw.(step) p.(step_allow) tid S (movers_impl.(compile_op) op);
        allowed_stable : 
          forall T (op : O1 T) T' (op' : O1 T') tid tid' S S' r evs,
            tid <> tid' ->
            p.(step_allow) T op tid S ->
            l1.(step) op' tid' S r S' evs ->
            p.(step_allow) T op tid S';
        (* This means that l1.step is either restricted_step or nilpotent_step *)
        raw_step_ok : 
          forall T (op : O1 T) tid S r S' evs,
            restricted_step l1raw.(step) p.(step_allow) op tid S r S' evs ->
            l1.(step) op tid S r S' evs;
        raw_initP_compat : forall S, l1raw.(initP) S -> l1.(initP) S;
      }.
  End S.
End LayerImplMoversProtocolT.

Module LayerImplMoversProtocol.
  Import Layer.
  Export LayerImplMoversT.
  Export LayerImplMoversProtocolT.
  Import Protocol.
  
  Section S.
    Context S
            `(l1raw : Layer.t O1 S) (l1: Layer.t O1 S)
            `(l2 : Layer.t O2 S)
            (p : Protocol.t O1 S)
            (a : LayerImplMoversProtocolT.t l1raw l1 l2 p).

    Definition absR (s1 : S) (s2 : S) := s1 = s2.

    Theorem absInitP :
      forall s1,
        l1raw.(initP) s1 ->
        exists s2, absR s1 s2 /\
                   l2.(initP) s2.
    Proof.
      unfold absR; init_abs; auto using a.(initP_compat), a.(raw_initP_compat).
    Qed.

    Definition compile_ts := Compile.compile_ts a.(compile_op).

    Theorem compile_ts_no_atomics :
      forall ts,
        no_atomics_ts ts ->
        no_atomics_ts (compile_ts ts).
    Proof.
      eapply Compile.compile_ts_no_atomics.
      eapply a.(compile_op_no_atomics).
    Qed.

    Theorem op_atomic : forall T (op : O2 T) `(rx : _ -> proc _ R),
        trace_incl l1.(step)
                        (Bind (a.(compile_op) op) rx)
                        (Bind (atomize a.(compile_op) op) rx).
    Proof.
      intros.
      eapply trace_incl_atomize_ysa.
      eapply a.(ysa_movers).
    Qed.

    Theorem atomize_correct :
      atomize_correct a.(compile_op) l1.(step).
    Proof.
      unfold atomize_correct; intros.
      rewrite op_atomic.
      eapply trace_incl_bind_a.
      eauto.
    Qed.

    Hint Resolve atomize_correct.

    Theorem all_traces_match :
      forall ts1 ts2,
        proc_match (Compile.compile_ok a.(compile_op)) ts1 ts2 ->
        traces_match_ts l1.(step) l2.(step) ts1 ts2.
    Proof.
      intros.
      eapply Compile.compile_traces_match_ts; eauto.
      eapply a.(compile_correct).
    Qed.

    Theorem compile_traces_match_l1 :
      forall ts2,
        no_atomics_ts ts2 ->
        traces_match_abs absR l1.(initP) l2.(initP) l1.(step) l2.(step) (compile_ts ts2) ts2.
    Proof.
      unfold traces_match_abs; init_abs.
      intuition auto using a.(initP_compat).
      eapply all_traces_match; eauto.
      eapply Compile.compile_ts_ok; eauto.
    Qed.

    Definition follows_protocol (ts : threads_state O1) :=
      forall s,
        follows_protocol_s l1raw.(step) p.(step_allow) ts s.

    Theorem compile_ts_follows_protocol :
      forall ts,
        no_atomics_ts ts ->
        follows_protocol (Compile.compile_ts a.(compile_op) ts).
    Proof.
      unfold follows_protocol.
      unfold follows_protocol_s.
      intros.
      eapply compile_ts_follows_protocol_proc; try eassumption.
      intros.

      eapply a.(op_follows_protocol).
    Qed.

    Lemma follows_protocol_s_spawn:
      forall (ts : threads_state _) (s : S) (T : Type) (tid tid' : nat)
             (p0 : proc O1 T) (s' : S) (evs : list event)
             (result : T + proc O1 T) (spawned : maybe_proc O1),
        tid <> tid' ->
        ts tid' = NoProc ->
        follows_protocol_s l1raw.(step) p.(step_allow) ts s ->
        exec_tid l1raw.(step) tid s p0 s' result spawned evs ->
        follows_protocol_proc l1raw.(step) p.(step_allow) tid s p0 ->
        follows_protocol_s l1raw.(step) p.(step_allow) (ts [[tid' := spawned]]) s.
    Proof.
      intros.
      destruct spawned; cycle 1.
      rewrite thread_upd_same_eq with (tid:=tid') in * by auto; eauto.
      unfold follows_protocol_s; intros.
      cmp_ts tid0 tid'; repeat maybe_proc_inv; eauto.
      remember (Proc p2).
      generalize dependent p2.
      generalize dependent tid'.
      induction H2; propositional; eauto; NoProc_upd;
        repeat maybe_proc_inv.
      invert H3.
      eapply IHexec_tid; eauto.
      invert H3; eauto.
    Qed.

    Lemma no_atomics_ts_exec_spawn:
      forall (ts : threads_state _) (s : S),
        no_atomics_ts ts ->
        forall (T : Type) (tid tid' : nat) (p0 : proc O1 T) (s' : S)
               (evs : list event) (result : T + proc O1 T) (T0 : Type)
               (p1 : proc O1 T0),
          ts tid = Proc p0 ->
          exec_tid l1raw.(step) tid s p0 s' result (Proc p1) evs ->
          no_atomics_ts (ts [[tid' := Proc p1]]).
    Proof.
      intros.
      eapply no_atomics_thread_upd_Proc; auto.
      assert (no_atomics p0).
      unfold no_atomics_ts in H.
      eapply thread_Forall_some with (a:=tid) in H; eauto.
      clear dependent ts.

      (* goal is now simplified to just be about one process *)
      remember (Proc p1).
      generalize dependent p1.
      induction H1; intros; repeat maybe_proc_inv; propositional.
      invert H2; eauto.
      invert H2.
    Qed.

    Theorem compile_traces_match_l1raw :
      forall ts,
        follows_protocol ts ->
        no_atomics_ts ts ->
        traces_match_abs absR l1raw.(initP) l1.(initP) l1raw.(step) l1.(step) ts ts.
    Proof.
      unfold compile_ts, follows_protocol, absR.
      unfold traces_match_abs; intros; subst.
      init_abs.
      intuition auto using a.(raw_initP_compat).
      clear H1.
      specialize (H sl).
      induction H2; eauto.
      cmp_ts tid tid'.
      pose proof (H tid _ p0 ltac:(eauto)) as Htid.

      prove_hyps IHexec.
      - eapply follows_protocol_s_exec_tid_upd; eauto.
        intros; eapply a.(allowed_stable); eauto.
        eapply a.(raw_step_ok); eauto.

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
        intros; apply a.(raw_step_ok); eauto.
        eapply follows_protocol_preserves_exec_tid'; eauto.
    Qed.

    Hint Resolve (_:Reflexive absR).
    Local Hint Resolve (_:Transitive absR).

    Local Hint Resolve compile_ts_no_atomics.
    Local Hint Resolve compile_ts_follows_protocol.

    Theorem compile_traces_match :
      forall ts,
        no_atomics_ts ts ->
        traces_match_abs absR l1raw.(initP) l2.(initP) l1raw.(step) l2.(step) (compile_ts ts) ts.
    Proof.
      unfold traces_match_abs; intros.
      eapply compile_traces_match_l1raw in H1; propositional; eauto.
      eapply compile_traces_match_l1 in H3; propositional; eauto.
    Qed.

    Theorem initP_compat : forall s,
        l1raw.(initP) s -> l2.(initP) s.
    Proof.
      auto using a.(initP_compat), a.(raw_initP_compat).
    Qed.

    Definition t : LayerImpl.t l1raw l2.
      refine {| LayerImpl.absR := absR;
                LayerImpl.absInitP := absInitP;
                LayerImpl.compile_ts := compile_ts;
                LayerImpl.compile_ts_no_atomics := compile_ts_no_atomics;
                LayerImpl.compile_traces_match := compile_traces_match; |}.
    Defined.

  End S.
End LayerImplMoversProtocol.

Module LayerImplLoopT.
  Import Layer.
  Section S.
    Context S
            `(l1: Layer.t O1 S)
            `(l2: Layer.t O2 S).

    Record t :=
      { compile_op : forall T, O2 T -> (option T -> O1 T) * (T -> bool) * option T;
        noop_or_success : noop_or_success compile_op l1.(step) l2.(step);
        initP_compat : forall s, l1.(initP) s -> l2.(initP) s; }.
  End S.
End LayerImplLoopT.

Module LayerImplLoop.
  Import Layer.
  Export LayerImplLoopT.
  Section S.
    Context S
            `(l1 : Layer.t O1 S)
            `(l2 : Layer.t O2 S)
            (a : LayerImplLoopT.t l1 l2).

    Definition absR (s1 : S) (s2 : S) := s1 = s2.

    Definition compile_ts ts :=
      CompileLoop.compile_ts a.(compile_op) ts.

    Theorem compile_ts_no_atomics :
      forall ts,
        no_atomics_ts ts ->
        no_atomics_ts (compile_ts ts).
    Proof.
      eapply CompileLoop.compile_ts_no_atomics.
    Qed.

    Theorem absInitP :
      forall s1,
        l1.(initP) s1 ->
        exists s2, absR s1 s2 /\
                   l2.(initP) s2.
    Proof.
      unfold absR; eauto using a.(initP_compat).
    Qed.

    Theorem compile_traces_match :
      forall ts,
        no_atomics_ts ts ->
        traces_match_abs absR l1.(initP) l2.(initP) l1.(step) l2.(step) (compile_ts ts) ts.
    Proof.
      unfold traces_match_abs, absR; intros; subst.
      init_abs.
      intuition auto using a.(initP_compat).
      eapply CompileLoop.compile_traces_match_ts; eauto.
      eapply a.(noop_or_success).
      eapply CompileLoop.compile_ts_ok; eauto.
    Qed.

    Definition t : LayerImpl.t l1 l2.
      refine {| LayerImpl.absR := absR;
                LayerImpl.absInitP := absInitP;
                LayerImpl.compile_ts := compile_ts;
                LayerImpl.compile_ts_no_atomics := compile_ts_no_atomics;
                LayerImpl.compile_traces_match := compile_traces_match; |}.
    Defined.
  End S.
End LayerImplLoop.

(** General layer transformers. *)

Module Link.
  Import Layer.
  Import LayerImpl.
  Section S.
    Context
      `(a: Layer.t OA SA)
      `(b: Layer.t OB SB)
      `(c: Layer.t OC SC)
      (x: LayerImpl.t a b)
      (y: LayerImpl.t b c).
    
    Definition link_absR (s1 : SA) (s3 : SC) :=
      exists s2, x.(absR) s1 s2 /\ y.(absR) s2 s3.

    Definition compile_ts ts :=
      x.(compile_ts) (y.(compile_ts) ts).

    Check compile_ts.
    Theorem link_compile_ts_no_atomics :
      forall ts,
        no_atomics_ts ts ->
        no_atomics_ts (compile_ts ts).
    Proof.
      intros.
      eapply x.(compile_ts_no_atomics).
      eapply y.(compile_ts_no_atomics).
      eauto.
    Qed.

    Theorem absInitP :
      forall s1,
        a.(initP) s1 ->
        exists s2, link_absR s1 s2 /\ c.(initP) s2.
    Proof.
      unfold link_absR; intros.
      eapply x.(absInitP) in H; propositional.
      eapply y.(absInitP) in H0; propositional.
      eauto.
    Qed.

    Lemma absR_transitive : forall s1 s2 s3,
        x.(absR) s1 s2 ->
        y.(absR) s2 s3 ->
        link_absR s1 s3.
    Proof.
      unfold link_absR; eauto.
    Qed.

    Hint Resolve absR_transitive.

    Theorem compile_traces_match :
      forall ts,
        no_atomics_ts ts ->
        traces_match_abs link_absR a.(initP) c.(initP) a.(step) c.(step) (compile_ts ts) ts.
    Proof.
      unfold traces_match_abs; intros.
      eapply x.(compile_traces_match) in H1; propositional; eauto.
      eapply y.(compile_traces_match) in H3; propositional; eauto.
      eapply y.(compile_ts_no_atomics); eauto.
    Qed.

    Definition t : LayerImpl.t a c.
      refine {| LayerImpl.absR := link_absR;
                LayerImpl.absInitP := absInitP;
                LayerImpl.compile_ts := compile_ts;
                LayerImpl.compile_ts_no_atomics := link_compile_ts_no_atomics;
                LayerImpl.compile_traces_match := compile_traces_match; |}.
    Defined.

  End S.
End Link.
