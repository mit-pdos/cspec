Require Import ConcurProc.
Require Import Equiv.
Require Import Helpers.Helpers.
Require Import FunctionalExtensionality.
Require Import Omega.
Require Import List.

Import ListNotations.

Global Set Implicit Arguments.
Global Generalizable All Variables.


Section Compiler.

  Variable opLoT : Type -> Type.
  Variable opMidT : Type -> Type.

  Variable compile_op : forall T, opMidT T -> proc opLoT T.

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
  | CompileLog : forall `(v : T),
    compile_ok (Log v) (Log v).

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
  | ACompileLog : forall `(v : T),
    atomic_compile_ok (Log v) (Log v).

  CoFixpoint compile T (p : proc opMidT T) : proc opLoT T :=
    match p with
    | Ret t => Ret t
    | Op op => compile_op op
    | Bind p1 p2 => Bind (compile p1) (fun r => compile (p2 r))
    | Log v => Log v
    | Atomic p => Atomic (compile p)
    end.

  Theorem compile_ok_compile :
    forall `(p : proc _ T), compile_ok (compile p) p.
  Proof.
  Admitted.

  Fixpoint compile_ts (ts : threads_state) : threads_state :=
    match ts with
    | nil => nil
    | t :: ts' =>
      match t with
      | NoProc => NoProc
      | Proc p => Proc (compile p)
      end :: compile_ts ts'
    end.

  Theorem compile_ts_ok :
    forall ts,
      proc_match compile_ok (compile_ts ts) ts.
  Proof.
    induction ts; intros.
    - unfold proc_match; simpl; intuition eauto.
      left.
      repeat rewrite thread_get_nil; eauto.
    - unfold proc_match in *; cbn; intuition eauto.
      destruct tid; subst.
      + repeat rewrite thread_get_0.
        destruct a.
        * right.
          do 3 eexists; intuition eauto.
          eapply compile_ok_compile.
        * left; eauto.
      + repeat rewrite thread_get_S.
        eapply H0.
  Qed.


  Variable State : Type.
  Variable lo_step : OpSemantics opLoT State.
  Variable hi_step : OpSemantics opMidT State.

  Definition compile_correct :=
    forall `(op : opMidT T) tid s v s' evs,
      atomic_exec lo_step (compile_op op) tid s v s' evs ->
      trace_eq (prepend tid evs TraceEmpty) TraceEmpty /\
      hi_step op tid s v s'.

  Variable compile_is_correct : compile_correct.


  Lemma atomic_compile_ok_exec_tid : forall T (p1 : proc _ T) p2,
    atomic_compile_ok p1 p2 ->
    forall tid s s' result evs,
      exec_tid lo_step tid s p1 s' result evs ->
      exists result' evs',
        exec_tid hi_step tid s p2 s' result' evs' /\
        trace_eq (prepend tid evs TraceEmpty) (prepend tid evs' TraceEmpty) /\
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
    induction 1; intros.

    - exec_tid_inv.
      eapply compile_is_correct in H6.
      do 2 eexists; intuition eauto.

    - exec_tid_inv.
      do 2 eexists; split.
      constructor.
      split.
      compute; eauto.
      eauto.

    - exec_tid_inv.
      eapply IHatomic_compile_ok in H12.
      repeat deex.

      destruct result0; destruct result'; try solve [ exfalso; eauto ].

      + do 2 eexists; split.
        eauto.
        split.
        eauto.
        subst; eauto.

      + do 2 eexists; split.
        eauto.
        split.
        eauto.
        constructor.
        eauto.
        eauto.

    - exec_tid_inv.
      do 2 eexists; split.
      constructor.
      split.
      compute; eauto.
      eauto.
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

    - eapply proc_match_pick with (tid := tid) in H2 as H'.
      intuition try congruence.
      repeat deex.
      rewrite H3 in H; inversion H; clear H; subst.
      repeat maybe_proc_inv.

      edestruct atomic_compile_ok_exec_tid; eauto.
      repeat deex.

      edestruct IHexec.
      shelve.
      intuition idtac.

      eexists; split.
      eapply ExecPrefixOne with (tid := tid).
        eauto.
        eauto.
        eauto.

      eapply trace_eq_prepend'; eauto.
      Unshelve.

      destruct result, x; simpl in *; try solve [ exfalso; eauto ].
      eapply proc_match_del; eauto.
      eapply proc_match_upd; eauto.
  Qed.

End Compiler.

Hint Constructors compile_ok.
Hint Constructors atomic_compile_ok.

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
  | AtomizeLog : forall `(v : T),
    atomize_ok (Log v) (Log v).


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
    induction 1; intros.
    - eauto.
    - eapply trace_incl_bind_a.
      eauto.
    - rewrite exec_equiv_bind_bind.
      rewrite exec_equiv_bind_bind.
      eapply IHatomize_ok.
      eauto.
    - eapply trace_incl_bind_a; eauto.
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

  Theorem atomize_ok_upto_trace_incl :
    forall n ts1' ts1,
    proc_match_upto n atomize_ok ts1 ts1' ->
      trace_incl_ts op_step ts1 ts1'.
  Proof.
    induction n; intros.
    - apply proc_match_upto_0_eq in H; subst.
      reflexivity.
    - destruct (lt_dec n (length ts1)).
      + etransitivity.
        instantiate (1 := thread_upd ts1' n (thread_get ts1 n)).
        * eapply IHn.
          eapply proc_match_upto_Sn in H; eauto.
        * eapply proc_match_upto_pick with (tid := n) in H; intuition idtac.
          edestruct H0. omega.
         -- intuition idtac.
            rewrite H2.
            rewrite <- exec_equiv_ts_upd_same; eauto.
            reflexivity.
         -- repeat deex.
            rewrite H.
            rewrite atomize_ok_trace_incl; eauto.
            rewrite thread_upd_same; eauto.
            reflexivity.
      + eapply IHn.
        eapply proc_match_upto_Sn'.
        omega.
        eauto.
  Qed.

  Theorem atomize_ok_trace_incl_ts :
    forall ts1' ts1,
    proc_match atomize_ok ts1 ts1' ->
      trace_incl_ts op_step ts1 ts1'.
  Proof.
    intros.
    eapply atomize_ok_upto_trace_incl.
    eapply proc_match_upto_all.
    eauto.
  Qed.

End Atomization.

Arguments atomize_ok {opLoT opMidT} compile_op [T].
Arguments atomize_correct {opLoT opMidT} compile_op [State] op_step.


Ltac compile_eq_step :=
  match goal with
  | |- ?x = _ =>
    rewrite frob_proc_eq with (p := x) at 1; simpl;
      try reflexivity; f_equal
  | _ =>
    apply functional_extensionality; intros
  end.

Theorem compile_op_eq : forall opLoT opMidT T (op : opMidT T) f,
  @compile opLoT opMidT f T (Op op) =
    f T op.
Proof.
  intros.
  compile_eq_step.
  destruct (f T op); congruence.
Qed.

Theorem compile_ret_eq : forall opLoT opMidT T (v : T) f,
  @compile opLoT opMidT f T (Ret v) = Ret v.
Proof.
  intros.
  compile_eq_step.
Qed.

Theorem compile_bind_eq : forall opLoT opMidT T1 T2 (p1 : proc opMidT T1) (p2 : _ -> proc opMidT T2) f,
  @compile opLoT opMidT f T2 (Bind p1 p2) =
    Bind (compile f p1) (fun x => compile f (p2 x)).
Proof.
  intros.
  compile_eq_step.
Qed.

Theorem compile_log_eq : forall opLoT opMidT T (v : T) f,
  @compile opLoT opMidT f T (Log v) = Log v.
Proof.
  intros.
  compile_eq_step.
Qed.


Theorem atomize_proc_match_helper :
  forall T `(p1 : proc opLoT T) `(p2 : proc opMidT T)
         compile_op,
  compile_ok compile_op p1 p2 ->
    atomize_ok compile_op p1 (compile (atomize compile_op) p2) /\
    atomic_compile_ok compile_op (compile (atomize compile_op) p2) p2.
Proof.
  induction 1; simpl; intros.
  - rewrite compile_op_eq.
    split; constructor.
  - rewrite compile_ret_eq.
    split; constructor.
  - rewrite compile_bind_eq.
    intuition idtac.
    constructor. eauto. intros. specialize (H1 x). intuition eauto.
    constructor. eauto. intros. specialize (H1 x). intuition eauto.
  - rewrite compile_log_eq.
    split; constructor.
Qed.

Hint Resolve proc_match_cons_Proc.
Hint Resolve proc_match_cons_NoProc.

Theorem atomize_proc_match :
  forall `(ts1 : @threads_state opLoT)
         `(ts2 : @threads_state opMidT)
         compile_op,
  proc_match (compile_ok compile_op) ts1 ts2 ->
  exists ts1',
    proc_match (atomize_ok compile_op) ts1 ts1' /\
    proc_match (atomic_compile_ok compile_op) ts1' ts2.
Proof.
  induction ts1; intros.
  - eapply proc_match_len in H.
    destruct ts2; simpl in *; try omega.
    eexists; split.
    eapply proc_match_nil.
    eapply proc_match_nil.
  - eapply proc_match_len in H as H'.
    destruct ts2; simpl in *; try omega.

    eapply proc_match_cons_inv in H.
    edestruct IHts1; intuition eauto.
    + exists (NoProc :: x); subst; intuition eauto.
    + repeat deex.
      edestruct (atomize_proc_match_helper H4).
      eexists (Proc _ :: x); intuition eauto.
Qed.

Theorem compile_traces_match_ts :
  forall `(ts1 : @threads_state opLoT)
         `(ts2 : @threads_state opMidT)
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
