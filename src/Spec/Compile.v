Require Import ConcurProc.
Require Import Equiv.
Require Import Helpers.Helpers.
Require Import FunctionalExtensionality.
Require Import Omega.
Require Import List.

Import ListNotations.

Global Set Implicit Arguments.
Global Generalizable All Variables.


Section NoAtomics.

  Variable opT : Type -> Type.

  Inductive no_atomics_n : forall T (p : proc opT T) (n : nat), Prop :=
  | NoAtomicsOp : forall `(op : opT T) n,
    no_atomics_n (Op op) (S n)
  | NoAtomicsRet : forall `(x : T) n,
    no_atomics_n (Ret x) (S n)
  | NoAtomicsBind : forall `(pa : proc opT T1) `(pb : T1 -> proc _ T2) n,
    no_atomics_n pa n ->
    (forall x, no_atomics_n (pb x) n) ->
    no_atomics_n (Bind pa pb) (S n)
  | NoAtomicsLog : forall `(v : T) n,
    no_atomics_n (Log v) (S n)
  | NoAtomicsZero : forall `(p : proc _ T),
    no_atomics_n p 0.

  Definition no_atomics T (p : proc opT T) :=
    forall n,
      no_atomics_n p n.

  Definition no_atomics_opt x :=
    match x with
    | NoProc => True
    | Proc p => no_atomics p
    end.

  Definition no_atomics_ts (ts : threads_state) :=
    Forall no_atomics_opt ts.


  Theorem no_atomics_inv_bind_a : forall `(p1 : proc _ T1) `(p2 : T1 -> proc _ T2),
    no_atomics (Bind p1 p2) ->
    no_atomics p1.
  Proof.
    unfold no_atomics; intros.
    specialize (H (S n)); inversion H; clear H; repeat sigT_eq.
    eauto.
  Qed.

  Theorem no_atomics_inv_bind_b : forall `(p1 : proc _ T1) `(p2 : T1 -> proc _ T2),
    no_atomics (Bind p1 p2) ->
    forall x, no_atomics (p2 x).
  Proof.
    unfold no_atomics; intros.
    specialize (H (S n)); inversion H; clear H; repeat sigT_eq.
    eauto.
  Qed.

  Theorem no_atomics_inv_atomic : forall `(p : proc _ T),
    no_atomics (Atomic p) ->
    False.
  Proof.
    intros.
    specialize (H 1); inversion H.
  Qed.

  Theorem no_atomics_ts_cons : forall p ts,
    no_atomics_ts (p :: ts) ->
    no_atomics_opt p /\ no_atomics_ts ts.
  Proof.
    intros.
    inversion H; intuition.
  Qed.

End NoAtomics.

Hint Resolve no_atomics_inv_bind_a.
Hint Resolve no_atomics_inv_bind_b.
Hint Resolve no_atomics_inv_atomic.


Section Compiler.

  Variable opLoT : Type -> Type.
  Variable opMidT : Type -> Type.

  Variable compile_op : forall T, opMidT T -> proc opLoT T.

  Definition atomize T (op : opMidT T) : proc opLoT T :=
    Atomic (compile_op op).

  Inductive compile_ok_n : forall T (p1 : proc opLoT T) (p2 : proc opMidT T) (n : nat), Prop :=
  | CompileOp : forall `(op : opMidT T) n,
    compile_ok_n (compile_op op) (Op op) (S n)
  | CompileRet : forall `(x : T) n,
    compile_ok_n (Ret x) (Ret x) (S n)
  | CompileBind : forall `(p1a : proc opLoT T1) (p2a : proc opMidT T1)
                         `(p1b : T1 -> proc _ T2) (p2b : T1 -> proc _ T2) n,
    compile_ok_n p1a p2a n ->
    (forall x, compile_ok_n (p1b x) (p2b x) n) ->
    compile_ok_n (Bind p1a p1b) (Bind p2a p2b) (S n)
  | CompileLog : forall `(v : T) n,
    compile_ok_n (Log v) (Log v) (S n)
  | CompileZero : forall T (p1 : proc _ T) (p2 : proc _ T),
    compile_ok_n p1 p2 0.

  Definition compile_ok T (p1 : proc opLoT T) (p2 : proc opMidT T) :=
    forall n,
      compile_ok_n p1 p2 n.

  Inductive atomic_compile_ok_n : forall T (p1 : proc opLoT T) (p2 : proc opMidT T) (n : nat), Prop :=
  | ACompileOp : forall `(op : opMidT T) n,
    atomic_compile_ok_n (Atomic (compile_op op)) (Op op) n
  | ACompileRet : forall `(x : T) n,
    atomic_compile_ok_n (Ret x) (Ret x) n
  | ACompileBind : forall `(p1a : proc opLoT T1) (p2a : proc opMidT T1)
                          `(p1b : T1 -> proc _ T2) (p2b : T1 -> proc _ T2) n,
    atomic_compile_ok_n p1a p2a n ->
    (forall x, atomic_compile_ok_n (p1b x) (p2b x) n) ->
    atomic_compile_ok_n (Bind p1a p1b) (Bind p2a p2b) (S n)
  | ACompileLog : forall `(v : T) n,
    atomic_compile_ok_n (Log v) (Log v) n
  | ACompileZero : forall T (p1 : proc _ T) (p2 : proc _ T),
    atomic_compile_ok_n p1 p2 0.

  Definition atomic_compile_ok T (p1 : proc opLoT T) (p2 : proc opMidT T) :=
    forall n,
      atomic_compile_ok_n p1 p2 n.


  Hint Constructors compile_ok_n.
  Hint Constructors atomic_compile_ok_n.


  Theorem compile_ok_inv_bind : forall `(p1a : proc _ T1) `(p1b : _ -> proc _ T2) p2a p2b,
    compile_ok (Bind p1a p1b) (Bind p2a p2b) ->
      compile_ok p1a p2a /\
      forall r, compile_ok (p1b r) (p2b r).
  Proof.
    split; intros.

    intro.
    specialize (H (S n)); inversion H; clear H; repeat sigT_eq.
    eauto.

    intro.
    specialize (H (S n)); inversion H; clear H; repeat sigT_eq.
    eauto.
  Qed.

  Theorem compile_ok_bind : forall `(p1a : proc opLoT T1) (p2a : proc opMidT T1)
                                   `(p1b : T1 -> proc _ T2) (p2b : T1 -> proc _ T2),
    compile_ok p1a p2a ->
    (forall x, compile_ok (p1b x) (p2b x)) ->
    compile_ok (Bind p1a p1b) (Bind p2a p2b).
  Proof.
    intros.
    intro.
    destruct n; eauto.
    constructor; eauto.
    intros.
    eapply H0.
  Qed.

  Theorem atomic_compile_ok_inv_bind : forall `(p1a : proc _ T1) `(p1b : _ -> proc _ T2) p2,
    atomic_compile_ok (Bind p1a p1b) p2 ->
    exists p2a p2b,
      p2 = Bind p2a p2b /\
      atomic_compile_ok p1a p2a /\
      forall r, atomic_compile_ok (p1b r) (p2b r).
  Proof.
    intros.
    specialize (H 1) as H'.
    inversion H'; clear H'; repeat sigT_eq.
    do 2 eexists; intuition.

    intro.
    specialize (H (S n)); inversion H; clear H; repeat sigT_eq.
    eauto.

    intro.
    specialize (H (S n)); inversion H; clear H; repeat sigT_eq.
    eauto.
  Qed.

  Theorem atomic_compile_ok_bind : forall `(p1a : proc opLoT T1) (p2a : proc opMidT T1)
                                          `(p1b : T1 -> proc _ T2) (p2b : T1 -> proc _ T2),
    atomic_compile_ok p1a p2a ->
    (forall x, atomic_compile_ok (p1b x) (p2b x)) ->
    atomic_compile_ok (Bind p1a p1b) (Bind p2a p2b).
  Proof.
    intros.
    intro.
    destruct n; eauto.
    constructor; eauto.
    intros.
    eapply H0.
  Qed.

  Hint Resolve atomic_compile_ok_bind.


  CoFixpoint compile T (p : proc opMidT T) : proc opLoT T :=
    match p with
    | Ret t => Ret t
    | Op op => compile_op op
    | Bind p1 p2 => Bind (compile p1) (fun r => compile (p2 r))
    | Log v => Log v
    | Atomic p => Atomic (compile p)
    end.

  Ltac compile_eq_step :=
    match goal with
    | |- ?x = _ =>
      rewrite frob_proc_eq with (p := x) at 1; simpl;
        try reflexivity; f_equal
    | _ =>
      apply functional_extensionality; intros
    end.

  Theorem compile_op_eq : forall T (op : _ T),
    compile (Op op) =
      compile_op op.
  Proof.
    intros.
    compile_eq_step.
    destruct (compile_op op); congruence.
  Qed.

  Theorem compile_ret_eq : forall T (v : T),
    compile (Ret v) = Ret v.
  Proof.
    intros.
    compile_eq_step.
  Qed.

  Theorem compile_bind_eq : forall T1 T2 (p1 : proc _ T1) (p2 : _ -> proc _ T2),
    compile (Bind p1 p2) =
      Bind (compile p1) (fun x => compile (p2 x)).
  Proof.
    intros.
    compile_eq_step.
  Qed.

  Theorem compile_log_eq : forall T (v : T),
    compile (Log v) = Log v.
  Proof.
    intros.
    compile_eq_step.
  Qed.

  Theorem compile_atomic_eq : forall T (p : proc _ T),
    compile (Atomic p) = Atomic (compile p).
  Proof.
    intros.
    compile_eq_step.
  Qed.


  Theorem compile_ok_compile :
    forall `(p : proc _ T),
      no_atomics p ->
      compile_ok (compile p) p.
  Proof.
    unfold compile_ok; intros.
    generalize dependent p.
    generalize dependent T.
    induction n; eauto; intros.
    destruct p.
    - rewrite compile_op_eq; eauto.
    - rewrite compile_ret_eq; eauto.
    - rewrite compile_bind_eq; eauto 20.
    - rewrite compile_log_eq; eauto.
    - exfalso; eauto.
  Qed.

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
      no_atomics_ts ts ->
      proc_match compile_ok (compile_ts ts) ts.
  Proof.
    induction ts; intros.
    - unfold proc_match; simpl; intuition eauto.
      left.
      repeat rewrite thread_get_nil; eauto.
    - apply no_atomics_ts_cons in H; intuition idtac.
      unfold proc_match in *; cbn; intuition eauto.
      destruct tid; subst.
      + repeat rewrite thread_get_0.
        destruct a.
        * simpl in *.
          right.
          do 3 eexists; intuition eauto.
          eapply compile_ok_compile; eauto.
        * left; eauto.
      + repeat rewrite thread_get_S.
        eapply H3.
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
    intros.
    induction H0.

    - specialize (H 1).
      inversion H; clear H; repeat sigT_eq.
      eauto.

    - specialize (H 1).
      inversion H.

    - specialize (H 1).
      inversion H; clear H; repeat sigT_eq.
      eapply compile_is_correct in H0.
      do 2 eexists; intuition eauto.

    - specialize (H 1).
      inversion H; clear H; repeat sigT_eq.
      eauto.

    - eapply atomic_compile_ok_inv_bind in H; repeat deex.
      edestruct IHexec_tid; eauto; repeat deex.
      do 2 eexists; intuition idtac.

      constructor; eauto.
      eauto.

      destruct result; destruct x; try solve [ exfalso; eauto ];
        subst; eauto.
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

Arguments atomize {opLoT opMidT} compile_op [T] op.


Section Atomization.

  (* [atomize_ok] captures the notion that all implementations of opcodes
     in the left-side proc have been replaced with atomic-bracketed
     versions in the right-side proc. *)

  Variable opLoT : Type -> Type.
  Variable opMidT : Type -> Type.
  Variable compile_op : forall T, opMidT T -> proc opLoT T.

  Inductive atomize_ok_n : forall T (p1 p2 : proc opLoT T) (n : nat), Prop :=
  | AtomizeOp : forall `(op : opMidT T) n,
    atomize_ok_n (compile_op op) (atomize compile_op op) (S n)
  | AtomizeRet : forall `(x : T) n,
    atomize_ok_n (Ret x) (Ret x) (S n)
  | AtomizeBind : forall T1 T2 (p1a p2a : proc opLoT T1)
                               (p1b p2b : T1 -> proc opLoT T2) n,
    atomize_ok_n p1a p2a n ->
    (forall x, atomize_ok_n (p1b x) (p2b x) n) ->
    atomize_ok_n (Bind p1a p1b) (Bind p2a p2b) (S n)
  | AtomizeLog : forall `(v : T) n,
    atomize_ok_n (Log v) (Log v) (S n)
  | AtomizeZero : forall `(p1 : proc _ T) p2,
    atomize_ok_n p1 p2 0.

  Definition atomize_ok T (p1 p2 : proc opLoT T) :=
    forall n,
      atomize_ok_n p1 p2 n.


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
(*
    intros.
    eapply trace_incl_proof_helper; intros.
    exec_tid_inv.

    generalize dependent p2.
    induction H12; intros.

    - specialize (H 1).
      inversion H; clear H; repeat sigT_eq.
      eauto.


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
*)
  Admitted.

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



Theorem atomize_proc_match_helper :
  forall T `(p1 : proc opLoT T) `(p2 : proc opMidT T)
         compile_op,
  compile_ok compile_op p1 p2 ->
    atomize_ok compile_op p1 (compile (atomize compile_op) p2) /\
    atomic_compile_ok compile_op (compile (atomize compile_op) p2) p2.
Proof.
  split; intro n; generalize dependent T.
  - induction n; intros; [ apply AtomizeZero | ].
    specialize (H (S n)) as H'; inversion H'; clear H'; repeat sigT_eq.

    + rewrite compile_op_eq. constructor.
    + rewrite compile_ret_eq. constructor.
    + rewrite compile_bind_eq. constructor.
      * eapply IHn. eapply compile_ok_inv_bind in H. intuition eauto.
      * intros.
        eapply IHn. eapply compile_ok_inv_bind in H. intuition eauto.
    + rewrite compile_log_eq. constructor.

  - induction n; intros; [ apply ACompileZero | ].
    specialize (H (S n)) as H'; inversion H'; clear H'; repeat sigT_eq.

    + rewrite compile_op_eq. constructor.
    + rewrite compile_ret_eq. constructor.
    + rewrite compile_bind_eq. constructor.
      * eapply IHn. eapply compile_ok_inv_bind in H. intuition eauto.
      * intros.
        eapply IHn. eapply compile_ok_inv_bind in H. intuition eauto.
    + rewrite compile_log_eq. constructor.
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
