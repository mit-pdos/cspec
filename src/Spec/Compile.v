Require Import ConcurProc.
Require Import Equiv ProcMatch.
Require Import Helpers.Helpers.
Require Import Helpers.FinMap.
Require Import FunctionalExtensionality.
Require Import Omega.
Require Import List.

Import ListNotations.

Global Set Implicit Arguments.
Global Generalizable All Variables.


Section ProcStructure.

  Variable opT : Type -> Type.

  Inductive no_atomics : forall T (p : proc opT T), Prop :=
  | NoAtomicsOp : forall `(op : opT T),
    no_atomics (Op op)
  | NoAtomicsRet : forall `(x : T),
    no_atomics (Ret x)
  | NoAtomicsBind : forall `(pa : proc opT T1) `(pb : T1 -> proc _ T2),
    no_atomics pa ->
    (forall x, no_atomics (pb x)) ->
    no_atomics (Bind pa pb)
  | NoAtomicsUntil : forall `(p : option T -> proc opT T) (c : T -> bool) v,
    (forall v, no_atomics (p v)) ->
    no_atomics (Until c p v)
  | NoAtomicsSpawn : forall `(p: proc opT T),
    no_atomics p ->
    no_atomics (Spawn p)
  .

  Hint Constructors no_atomics.

  Definition no_atomics_opt x :=
    match x with
    | NoProc => True
    | Proc p => no_atomics p
    end.

  Definition no_atomics_ts (ts : threads_state _) :=
    thread_Forall no_atomics ts.

  Theorem no_atomics_ts_equiv : forall ts,
    no_atomics_ts ts <->
    (forall tid, no_atomics_opt (ts [[ tid ]])).
  Proof.
    unfold no_atomics_ts, thread_Forall; split; intros.
    - destruct_with_eqn (ts tid); simpl; eauto.
      eapply thread_Forall_some in H; eauto.
    - unfold no_atomics_opt in *.
      eapply thread_Forall_forall; intros.
      specialize (H tid).
      rewrite H0 in *; eauto.
  Qed.

  Theorem no_atomics_thread_get : forall `(p : proc _ T) ts tid,
    no_atomics_ts ts ->
    ts [[ tid ]] = Proc p ->
    no_atomics p.
  Proof.
    unfold no_atomics_ts; intros.
    eapply thread_Forall_some; eauto.
  Qed.

  Theorem no_atomics_thread_upd_NoProc : forall ts tid,
    no_atomics_ts ts ->
    no_atomics_ts (ts [[ tid := NoProc ]]).
  Proof.
    unfold no_atomics_ts; intros.
    eauto using thread_Forall_upd_none.
  Qed.

  Theorem no_atomics_thread_upd_Proc : forall ts tid `(p : proc _ T),
    no_atomics_ts ts ->
    no_atomics p ->
    no_atomics_ts (ts [[ tid := Proc p ]]).
  Proof.
    unfold no_atomics_ts; intros.
    eauto using thread_Forall_upd_some.
  Qed.

  Theorem no_atomics_exec_tid :
    forall `(step : OpSemantics opT State) tid s `(p : proc _ T) s' p' spawned evs,
    no_atomics p ->
    exec_tid step tid s p s' (inr p') spawned evs ->
    no_atomics p'.
  Proof.
    intros.
    remember (inr p').
    induction H0; try congruence;
      inversion Heqs0; clear Heqs0; subst.
    - inversion H; clear H; subst; repeat sigT_eq.
      destruct result; eauto.
    - inversion H; clear H; subst; repeat sigT_eq.
      constructor; eauto; intros.
      destruct (Bool.bool_dec (c x) true); eauto.
  Qed.

End ProcStructure.

Hint Constructors no_atomics.
Hint Resolve no_atomics_thread_get.
Hint Resolve no_atomics_thread_upd_NoProc.
Hint Resolve no_atomics_thread_upd_Proc.
Hint Resolve no_atomics_exec_tid.


Section Compiler.

  Variable opLoT : Type -> Type.
  Variable opMidT : Type -> Type.

  Variable compile_op : forall T, opMidT T -> proc opLoT T.

  Variable compile_op_no_atomics :
    forall `(op : opMidT T),
      no_atomics (compile_op op).

  Definition atomize T (op : opMidT T) : proc opLoT T :=
    Atomic (compile_op op).

  Inductive compile_ok : forall T (p1 : proc opLoT T) (p2 : proc opMidT T), Prop :=
  | CompileOp : forall `(op : opMidT T),
    compile_ok (compile_op op) (Op op)
  | CompileRet : forall `(x : T),
    compile_ok (Ret x) (Ret x)
  | CompileBind : forall `(p1a : proc opLoT T1) (p2a : proc opMidT T1)
                         `(p1b : T1 -> proc _ T2) (p2b : T1 -> proc _ T2),
    compile_ok p1a p2a ->
    (forall x, compile_ok (p1b x) (p2b x)) ->
    compile_ok (Bind p1a p1b) (Bind p2a p2b)
  | CompileUntil : forall `(p1 : option T -> proc opLoT T) (p2 : option T -> proc opMidT T) (c : T -> bool) v,
    (forall v', compile_ok (p1 v') (p2 v')) ->
    compile_ok (Until c p1 v) (Until c p2 v)
  | CompileSpawn : forall T (p1: proc opLoT T) (p2: proc opMidT T),
      compile_ok p1 p2 ->
      compile_ok (Spawn p1) (Spawn p2)
  .

  Inductive atomic_compile_ok : forall T (p1 : proc opLoT T) (p2 : proc opMidT T), Prop :=
  | ACompileOp : forall `(op : opMidT T),
    atomic_compile_ok (Atomic (compile_op op)) (Op op)
  | ACompileRet : forall `(x : T),
    atomic_compile_ok (Ret x) (Ret x)
  | ACompileBind : forall `(p1a : proc opLoT T1) (p2a : proc opMidT T1)
                          `(p1b : T1 -> proc _ T2) (p2b : T1 -> proc _ T2),
    atomic_compile_ok p1a p2a ->
    (forall x, atomic_compile_ok (p1b x) (p2b x)) ->
    atomic_compile_ok (Bind p1a p1b) (Bind p2a p2b)
  | ACompileUntil : forall `(p1 : option T -> proc opLoT T) (p2 : option T -> proc opMidT T) (c : T -> bool) v,
    (forall v', atomic_compile_ok (p1 v') (p2 v')) ->
    atomic_compile_ok (Until c p1 v) (Until c p2 v)
  | ACompileSpawn : forall T (p1: proc opLoT T) (p2: proc opMidT T),
      atomic_compile_ok p1 p2 ->
      atomic_compile_ok (Spawn p1) (Spawn p2)
  .

  Hint Constructors compile_ok.
  Hint Constructors atomic_compile_ok.


  Fixpoint compile T (p : proc opMidT T) : proc opLoT T :=
    match p with
    | Ret t => Ret t
    | Op op => compile_op op
    | Bind p1 p2 => Bind (compile p1) (fun r => compile (p2 r))
    | Atomic p => Atomic (compile p)
    | Until c p v => Until c (fun r => compile (p r)) v
    | Spawn p => Spawn (compile p)
    end.


  Theorem compile_ok_compile :
    forall `(p : proc _ T),
      no_atomics p ->
      compile_ok (compile p) p.
  Proof.
    induct p; simpl; eauto.
    - invert H0; eauto.
    - invert H0; eauto.
    - invert H.
    - invert H; eauto.
  Qed.

  Theorem compile_no_atomics :
    forall `(p : proc _ T),
      no_atomics p ->
      no_atomics (compile p).
  Proof.
    (* TODO: this eauto takes forever to fail *)
    induct p; simpl; eauto.
    - invert H0; eauto.
    - invert H0; eauto.
    - invert H.
    - invert H; eauto.
  Qed.

  Hint Resolve compile_no_atomics.

  Definition compile_ts ts :=
    thread_map compile ts.

  Hint Resolve compile_ok_compile.

  Theorem compile_ts_ok :
    forall ts,
      no_atomics_ts ts ->
      proc_match compile_ok (compile_ts ts) ts.
  Proof.
    intros.
    apply proc_match_sym.
    unfold proc_match; intros.
    unfold compile_ts.
    destruct_with_eqn (ts tid).
    rewrite thread_map_get.
    destruct_with_eqn (ts tid); try congruence.
    invert Heqm; eauto.
    rewrite thread_map_get.
    simpl_match; auto.
  Qed.

  Theorem compile_ts_no_atomics :
    forall ts,
      no_atomics_ts ts ->
      no_atomics_ts (compile_ts ts).
  Proof.
    unfold no_atomics_ts, compile_ts; intros.
    eapply thread_map_Forall; eauto.
  Qed.

  Variable State : Type.
  Variable lo_step : OpSemantics opLoT State.
  Variable hi_step : OpSemantics opMidT State.

  Definition compile_correct :=
    forall T (op : opMidT T) tid s v s' evs,
      atomic_exec lo_step (compile_op op) tid s v s' evs ->
      hi_step op tid s v s' evs.

  Variable compile_is_correct : compile_correct.

  Lemma atomic_compile_ok_exec_tid : forall T (p1 : proc _ T) p2,
    atomic_compile_ok p1 p2 ->
    forall tid s s' result spawned evs,
      exec_tid lo_step tid s p1 s' result spawned evs ->
      exists result' spawned' evs',
        exec_tid hi_step tid s p2 s' result' spawned' evs' /\
        evs = evs' /\
        proc_optR atomic_compile_ok spawned spawned' /\
        match result with
        | inl v => match result' with
          | inl v' => v = v'
          | inr _ => False
          end
        | inr p' => match result' with
          | inl _ => False
          | inr p'' => atomic_compile_ok p' p''
          end
        end.
  Proof.
    intros.
    induct H0.
    all: invert H; eauto 10.

    - edestruct IHexec_tid; eauto; repeat deex.
      descend; intuition eauto.
      destruct matches; propositional; eauto.

    - descend; intuition eauto.

      constructor; propositional; eauto.
      destruct matches.
  Qed.

  Lemma proc_match_none : forall tid `(ts1: threads_state opT) `(ts2: threads_state opT') R,
      proc_match R ts1 ts2 ->
      ts1 tid = NoProc ->
      ts2 tid = NoProc.
  Proof.
    intros.
    specialize (H tid); simpl_match; auto.
  Qed.

  Theorem atomic_compile_ok_traces_match_ts :
    forall ts1 ts2,
      proc_match atomic_compile_ok ts1 ts2 ->
      traces_match_ts lo_step hi_step ts1 ts2.
  Proof.
    unfold traces_match_ts; intros.
    generalize dependent ts2.
    unfold exec_prefix in H0; repeat deex.
    induction H; intros; eauto.

    - eapply proc_match_pick with (tid := tid) in H3 as H'.
      intuition try congruence.
      repeat deex.
      replace (ts tid) in H; invert H.
      repeat maybe_proc_inv.

      edestruct atomic_compile_ok_exec_tid; eauto.
      repeat deex.
      assert (ts2 tid' = NoProc) by eauto using proc_match_none.
      ExecPrefix tid tid'.
      eapply IHexec.
      destruct matches; propositional;
        eauto using proc_match_del, proc_match_upd, proc_match_upd_opt.
  Qed.

End Compiler.

Arguments atomize {opLoT opMidT} compile_op [T] op.


Section Atomization.

  (* [atomize_ok] captures the notion that all implementations of opcodes
     in the left-side proc have been replaced with atomic-bracketed
     versions in the right-side proc. *)

  Variable opLoT : Type -> Type.
  Variable opMidT : Type -> Type.
  Variable compile_op : forall T, opMidT T -> proc opLoT T.

  Inductive atomize_ok : forall T (p1 p2 : proc opLoT T), Prop :=
  | AtomizeOp : forall `(op : opMidT T),
    atomize_ok (compile_op op) (atomize compile_op op)
  | AtomizeRet : forall `(x : T),
    atomize_ok (Ret x) (Ret x)
  | AtomizeBind : forall T1 T2 (p1a p2a : proc opLoT T1)
                               (p1b p2b : T1 -> proc opLoT T2),
    atomize_ok p1a p2a ->
    (forall x, atomize_ok (p1b x) (p2b x)) ->
    atomize_ok (Bind p1a p1b) (Bind p2a p2b)
  | AtomizeUntil : forall T (p1 p2 : option T -> proc opLoT T) (c : T -> bool) v,
    (forall v', atomize_ok (p1 v') (p2 v')) ->
    atomize_ok (Until c p1 v) (Until c p2 v)
  | AtomizeSpawn : forall T (p1 p2: proc opLoT T),
      atomize_ok p1 p2 ->
      atomize_ok (Spawn p1) (Spawn p2)
  .


  Variable State : Type.
  Variable op_step : OpSemantics opLoT State.

  Definition atomize_correct :=
    forall T (op : opMidT T)
           T' (p1rest p2rest : _ -> proc _ T'),
           (forall x, trace_incl op_step (p1rest x) (p2rest x)) ->
           trace_incl op_step
             (Bind (compile_op op) p1rest)
             (Bind (atomize compile_op op) p2rest).

  Variable atomize_is_correct : atomize_correct.

  Theorem atomize_ok_trace_incl_0 :
    forall T p1 p2,
    atomize_ok p1 p2 ->
    forall T' (p1rest p2rest : T -> proc _ T'),
    (forall x, trace_incl op_step (p1rest x) (p2rest x)) ->
    trace_incl op_step (Bind p1 p1rest) (Bind p2 p2rest).
  Proof.
    induction 1; intros; eauto.
    - eapply trace_incl_bind_a; eauto.
    - repeat rewrite exec_equiv_bind_bind.
      eauto.
    - etransitivity.
      eapply trace_incl_rx_to_trace_incl.
      eapply trace_incl_rx_until.
      intros. eapply trace_incl_to_trace_incl_rx; intros.
      eapply H0; intros.
      reflexivity.
      eapply trace_incl_bind_a; intros.
      eauto.
    - etransitivity.
      eapply trace_incl_rx_to_trace_incl.
      eapply trace_incl_rx_spawn.
      eapply trace_incl_to_trace_incl_rx; intros.
      eapply IHatomize_ok; reflexivity.
      eapply trace_incl_bind_a; intros.
      eauto.
  Qed.

  Theorem atomize_ok_trace_incl :
    forall `(p1 : proc _ T) p2,
    atomize_ok p1 p2 ->
    trace_incl op_step p1 p2.
  Proof.
    intros.
    rewrite <- exec_equiv_bind_ret.
    rewrite <- exec_equiv_bind_ret with (p := p2).
    eapply atomize_ok_trace_incl_0; eauto.
    reflexivity.
  Qed.

  Theorem atomize_ok_trace_incl_ts :
    forall ts1' ts1,
    proc_match atomize_ok ts1 ts1' ->
    trace_incl_ts op_step ts1 ts1'.
  Proof.
    intros.
    eapply trace_incl_ts_proc_match.
    eapply proc_match_subrelation;
      eauto using atomize_ok_trace_incl.
  Qed.

End Atomization.

Arguments atomize_ok {opLoT opMidT} compile_op [T].
Arguments atomize_correct {opLoT opMidT} compile_op [State] op_step.



Theorem atomize_proc_match_helper :
  forall T `(p1 : proc opLoT T) `(p2 : proc opMidT T)
         compile_op,
  compile_ok compile_op p1 p2 ->
    atomize_ok compile_op p1 (compile (atomize compile_op) p2) /\
    atomic_compile_ok compile_op (compile (atomize compile_op) p2) p2.
Proof.
  induction 1; simpl; intros.
  - split; constructor.
  - split; constructor.
  - intuition idtac.
    constructor. eauto. intros. specialize (H1 x). intuition eauto.
    constructor. eauto. intros. specialize (H1 x). intuition eauto.
  - split; constructor; intuition eauto;
      edestruct H0; eauto.
  - split; constructor; intuition eauto.
Qed.

Theorem atomize_proc_match :
  forall `(ts1 : threads_state opLoT)
         `(ts2 : threads_state opMidT)
         compile_op,
  proc_match (compile_ok compile_op) ts1 ts2 ->
  exists ts1',
    proc_match (atomize_ok compile_op) ts1 ts1' /\
    proc_match (atomic_compile_ok compile_op) ts1' ts2.
Proof.
  intros.
  exists (thread_map (compile (atomize compile_op)) ts2).
  eapply proc_match_subrelation in H;
    [ | intros; eapply atomize_proc_match_helper; eauto ].
  split.
  - eapply proc_match_map2.
    eapply proc_match_subrelation; eauto; simpl; propositional.
  - unfold proc_match; intros.
    specialize (H tid).
    rewrite thread_map_get.
    destruct matches in *|-; propositional;
      repeat simpl_match; repeat maybe_proc_inv;
        eauto.
Qed.

Theorem compile_traces_match_ts :
  forall `(ts1 : threads_state opLoT)
         `(ts2 : threads_state opMidT)
         `(lo_step : OpSemantics opLoT State) hi_step compile_op,
  compile_correct compile_op lo_step hi_step ->
  atomize_correct compile_op lo_step ->
  proc_match (compile_ok compile_op) ts1 ts2 ->
  traces_match_ts lo_step hi_step ts1 ts2.
Proof.
  intros.
  eapply atomize_proc_match in H1; deex.
  rewrite atomize_ok_trace_incl_ts; eauto.
  eapply atomic_compile_ok_traces_match_ts; eauto.
Qed.

Ltac trace_incl_simple :=
  solve [ unfold atomize; simpl; rewrite trace_incl_op;
          eapply trace_incl_bind_a; eauto ].
