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
  Variable opHiT : Type -> Type.

  Variable compile_op : forall T, opMidT T -> proc opLoT opHiT T.

  Definition atomize T (op : opMidT T) : proc opLoT opHiT T :=
    Atomic (compile_op op).

  Inductive compile_ok : forall T (p1 : proc opLoT opHiT T) (p2 : proc opMidT opHiT T), Prop :=
  | CompileOpcode : forall `(op : opMidT T),
    compile_ok (compile_op op) (Op op)
  | CompileRet : forall `(x : T),
    compile_ok (Ret x) (Ret x)
  | CompileBind : forall `(p1a : proc opLoT opHiT T1) (p2a : proc opMidT opHiT T1)
                         `(p1b : T1 -> proc _ _ T2) (p2b : T1 -> proc _ _ T2),
    compile_ok p1a p2a ->
    (forall x, compile_ok (p1b x) (p2b x)) ->
    compile_ok (Bind p1a p1b) (Bind p2a p2b)
  | CompileOpCallHi : forall `(op : opHiT T),
    compile_ok (OpCallHi op) (OpCallHi op)
  | CompileOpRetHi : forall `(v : T),
    compile_ok (OpRetHi v) (OpRetHi v).

  (* [atomic_compile_ok] is not quite [compile_ok] with [atomize]
     added to [compile_op].  It also breaks out [OpCall] and [OpRet]
     into separate matches, so that the [atomic_compile_ok] relation keeps
     holding across atomic steps taken by each thread.

     This means that [atomic_compile_ok] does not enforce the calling
     convention in itself: a program might have way too many [OpCall]s
     and not enough [OpRet]s, etc.
   *)
  Inductive atomic_compile_ok : forall T (p1 : proc opLoT opHiT T) (p2 : proc opMidT opHiT T), Prop :=
  | ACompileOpCall : forall `(op : opMidT T),
    atomic_compile_ok (Ret tt) (OpCall op)
  | ACompileOpExec : forall `(op : opMidT T),
    atomic_compile_ok (Atomic (compile_op op)) (OpExec op)
  | ACompileOpRet : forall `(v : T),
    atomic_compile_ok (Ret v) (OpRet v)
  | ACompileRet : forall `(x : T),
    atomic_compile_ok (Ret x) (Ret x)
  | ACompileBind : forall `(p1a : proc opLoT opHiT T1) (p2a : proc opMidT opHiT T1)
                         `(p1b : T1 -> proc _ _ T2) (p2b : T1 -> proc _ _ T2),
    atomic_compile_ok p1a p2a ->
    (forall x, atomic_compile_ok (p1b x) (p2b x)) ->
    atomic_compile_ok (Bind p1a p1b) (Bind p2a p2b)
  | ACompileOpCallHi : forall `(op : opHiT T),
    atomic_compile_ok (OpCallHi op) (OpCallHi op)
  | ACompileOpRetHi : forall `(v : T),
    atomic_compile_ok (OpRetHi v) (OpRetHi v).

  CoFixpoint compile T (p : proc opMidT opHiT T) : proc opLoT opHiT T :=
    match p with
    | Ret t => Ret t
    | OpCall op => Ret tt
    | OpExec op => compile_op op
    | OpRet r => Ret r
    | Bind p1 p2 => Bind (compile p1) (fun r => compile (p2 r))
    | OpCallHi op => OpCallHi op
    | OpRetHi v => OpRetHi v
    | Atomic p => Atomic (compile p)
    end.

  Theorem compile_ok_compile :
    forall `(p : proc _ _ T), compile_ok (compile p) p.
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
      trace_match_hi (prepend tid evs TraceEmpty) (@TraceEmpty opMidT opHiT) /\
      hi_step op tid s v s'.

  Variable compile_is_correct : compile_correct.


  Lemma atomic_compile_ok_exec_tid : forall T (p1 : proc _ _ T) p2,
    atomic_compile_ok p1 p2 ->
    forall tid s s' result evs,
      exec_tid lo_step tid s p1 s' result evs ->
      exists result' evs',
        exec_tid hi_step tid s p2 s' result' evs' /\
        trace_match_hi (prepend tid evs TraceEmpty) (prepend tid evs' TraceEmpty) /\
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
      do 2 eexists; split.
      constructor.
      split.
      compute; eauto.
      eauto.

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

      eapply trace_match_hi_prepend'; eauto.
      Unshelve.

      destruct result, x; simpl in *; try solve [ exfalso; eauto ].
      eapply proc_match_del; eauto.
      eapply proc_match_upd; eauto.

    - eexists; split.
      eauto.
      reflexivity.
  Qed.

End Compiler.

Hint Constructors compile_ok.
Hint Constructors atomic_compile_ok.

Arguments atomize {opLoT opMidT opHiT} compile_op [T] op.


Section Atomization.

  (* [atomize_ok] captures the notion that all implementations of opcodes
     in the left-side proc have been replaced with atomic-bracketed
     versions in the right-side proc. *)

  Variable opLoT : Type -> Type.
  Variable opMidT : Type -> Type.
  Variable opHiT : Type -> Type.
  Variable compile_op : forall T, opMidT T -> proc opLoT opHiT T.

  Inductive atomize_ok : forall T (p1 p2 : proc opLoT opHiT T), Prop :=
  | AtomizeOpcode : forall `(op : opMidT T),
    atomize_ok (compile_op op) (_ <- Ret tt; r <- atomize compile_op op; Ret r)
  | AtomizeRet : forall `(x : T),
    atomize_ok (Ret x) (Ret x)
  | AtomizeBind : forall T1 T2 (p1a p2a : proc opLoT opHiT T1)
                               (p1b p2b : T1 -> proc opLoT opHiT T2),
    atomize_ok p1a p2a ->
    (forall x, atomize_ok (p1b x) (p2b x)) ->
    atomize_ok (Bind p1a p1b) (Bind p2a p2b)
  | AtomizeOpCallHi : forall `(op : opHiT T),
    atomize_ok (OpCallHi op) (OpCallHi op)
  | AtomizeOpRetHi : forall `(v : T),
    atomize_ok (OpRetHi v) (OpRetHi v).


  Variable State : Type.
  Variable op_step : OpSemantics opLoT State.

  Definition atomize_correct :=
    forall T (op : opMidT T)
           T' (p1rest p2rest : _ -> proc _ _ T'),
           (forall x, hitrace_incl op_step (p1rest x) (p2rest x)) ->
           hitrace_incl op_step
             (Bind (compile_op op) p1rest)
             (Bind (atomize compile_op op) p2rest).

  Variable atomize_is_correct : atomize_correct.


  Theorem atomize_ok_hitrace_incl_0 :
    forall T p1 p2,
    atomize_ok p1 p2 ->
    forall T' (p1rest p2rest : T -> proc _ _ T'),
    (forall x, hitrace_incl op_step (p1rest x) (p2rest x)) ->
    hitrace_incl op_step (Bind p1 p1rest) (Bind p2 p2rest).
  Proof.
    induction 1; intros.
    - eauto.
      unfold atomize_correct in atomize_is_correct.
      rewrite atomize_is_correct; eauto.
      rewrite exec_equiv_bind_bind.
      rewrite exec_equiv_ret_bind.
      rewrite exec_equiv_bind_bind.
      setoid_rewrite exec_equiv_ret_bind.
      reflexivity.
    - eapply hitrace_incl_bind_a.
      eauto.
    - rewrite exec_equiv_bind_bind.
      rewrite exec_equiv_bind_bind.
      eapply IHatomize_ok.
      eauto.
    - eapply hitrace_incl_bind_a; eauto.
    - eapply hitrace_incl_bind_a; eauto.
  Qed.

  Theorem atomize_ok_hitrace_incl :
    forall `(p1 : proc _ _ T) p2,
    atomize_ok p1 p2 ->
    hitrace_incl op_step p1 p2.
  Proof.
    intros.
    rewrite <- exec_equiv_bind_ret.
    rewrite <- exec_equiv_bind_ret with (p := p2).
    eapply atomize_ok_hitrace_incl_0; eauto.
    reflexivity.
  Qed.

  Theorem atomize_ok_upto_hitrace_incl :
    forall n ts1' ts1,
    proc_match_upto n atomize_ok ts1 ts1' ->
      hitrace_incl_ts op_step ts1 ts1'.
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
            rewrite atomize_ok_hitrace_incl; eauto.
            rewrite thread_upd_same; eauto.
            reflexivity.
      + eapply IHn.
        eapply proc_match_upto_Sn'.
        omega.
        eauto.
  Qed.

  Theorem atomize_ok_hitrace_incl_ts :
    forall ts1' ts1,
    proc_match atomize_ok ts1 ts1' ->
      hitrace_incl_ts op_step ts1 ts1'.
  Proof.
    intros.
    eapply atomize_ok_upto_hitrace_incl.
    eapply proc_match_upto_all.
    eauto.
  Qed.

End Atomization.

Arguments atomize_ok {opLoT opMidT opHiT} compile_op [T].
Arguments atomize_correct {opLoT opMidT opHiT} compile_op [State] op_step.


Ltac compile_eq_step :=
  match goal with
  | |- ?x = _ =>
    rewrite frob_proc_eq with (p := x) at 1; simpl;
      try reflexivity; f_equal
  | _ =>
    apply functional_extensionality; intros
  end.

Theorem compile_op_eq : forall opLoT opMidT opHiT T (op : opMidT T) f,
  @compile opLoT opMidT opHiT f T (Op op) =
    _ <- Ret tt; r <- f T op; Ret r.
Proof.
  intros.
  compile_eq_step.
  compile_eq_step.
  compile_eq_step.
  compile_eq_step.
  compile_eq_step.
  destruct (f T op); congruence.
  repeat compile_eq_step.
Qed.

Theorem compile_ret_eq : forall opLoT opMidT opHiT T (v : T) f,
  @compile opLoT opMidT opHiT f T (Ret v) = Ret v.
Proof.
  intros.
  compile_eq_step.
Qed.

Theorem compile_bind_eq : forall opLoT opMidT opHiT T1 T2 (p1 : proc opMidT opHiT T1) (p2 : _ -> proc opMidT opHiT T2) f,
  @compile opLoT opMidT opHiT f T2 (Bind p1 p2) =
    Bind (compile f p1) (fun x => compile f (p2 x)).
Proof.
  intros.
  compile_eq_step.
Qed.

Theorem compile_callhi_eq : forall opLoT opMidT opHiT T (op : opHiT T) f,
  @compile opLoT opMidT opHiT f _ (OpCallHi op) = OpCallHi op.
Proof.
  intros.
  compile_eq_step.
Qed.

Theorem compile_rethi_eq : forall opLoT opMidT opHiT T (v : T) f,
  @compile opLoT opMidT opHiT f T (OpRetHi v) = OpRetHi v.
Proof.
  intros.
  compile_eq_step.
Qed.


Theorem atomize_proc_match_helper :
  forall T `(p1 : proc opLoT opHiT T) `(p2 : proc opMidT opHiT T)
         compile_op,
  compile_ok compile_op p1 p2 ->
    atomize_ok compile_op p1 (compile (atomize compile_op) p2) /\
    atomic_compile_ok compile_op (compile (atomize compile_op) p2) p2.
Proof.
  induction 1; simpl; intros.
  - rewrite compile_op_eq.
    split.
    constructor.
    repeat constructor.
  - rewrite compile_ret_eq.
    split; constructor.
  - rewrite compile_bind_eq.
    intuition idtac.
    constructor. eauto. intros. specialize (H1 x). intuition eauto.
    constructor. eauto. intros. specialize (H1 x). intuition eauto.
  - rewrite compile_callhi_eq.
    split; constructor.
  - rewrite compile_rethi_eq.
    split; constructor.
Qed.

Hint Resolve proc_match_cons_Proc.
Hint Resolve proc_match_cons_NoProc.

Theorem atomize_proc_match :
  forall `(ts1 : @threads_state opLoT opHiT)
         `(ts2 : @threads_state opMidT opHiT)
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
  forall `(ts1 : @threads_state opLoT opHiT)
         `(ts2 : @threads_state opMidT opHiT)
         `(lo_step : OpSemantics opLoT State) hi_step compile_op,
  compile_correct compile_op lo_step hi_step ->
  atomize_correct compile_op lo_step ->
  proc_match (compile_ok compile_op) ts1 ts2 ->
  traces_match_ts lo_step hi_step ts1 ts2.
Proof.
  intros.
  eapply atomize_proc_match in H1; deex.
  rewrite atomize_ok_hitrace_incl_ts; eauto.
  eapply atomic_compile_ok_traces_match_ts; eauto.
Qed.


Section Movers.

  Variable opT : Type -> Type.
  Variable opHiT : Type -> Type.
  Variable State : Type.
  Variable op_step : OpSemantics opT State.

  Variable moverT : Type.
  Variable opMover : opT moverT.

  Definition always_enabled :=
    forall tid s,
      exists r s',
        op_step opMover tid s r s'.

  Definition right_mover :=
    forall `(op1 : opT T2) tid0 tid1 s s0 s1 v0 v1,
      tid0 <> tid1 ->
      op_step opMover tid0 s v0 s0 ->
      op_step op1 tid1 s0 v1 s1 ->
      exists s',
        op_step op1 tid1 s v1 s' /\
        op_step opMover tid0 s' v0 s1.

  Definition left_mover :=
    always_enabled /\
    forall `(op0 : opT T0) tid0 tid1 s s0 s1 v0 v1,
      tid0 <> tid1 ->
      op_step op0 tid0 s v0 s0 ->
      op_step opMover tid1 s0 v1 s1 ->
      exists s',
        op_step opMover tid1 s v1 s' /\
        op_step op0 tid0 s' v0 s1.

  Definition both_mover := right_mover /\ left_mover.

  Theorem both_mover_left : both_mover -> left_mover.
  Proof. unfold both_mover; intuition. Qed.

  Theorem both_mover_right : both_mover -> right_mover.
  Proof. unfold both_mover; intuition. Qed.


  Lemma atomic_exec_right_mover : forall tid0 tid1 s s0 `(ap : proc opT opHiT T) s1 v1 evs v0,
    right_mover ->
    tid0 <> tid1 ->
    op_step opMover tid0 s v0 s0 ->
    atomic_exec op_step ap tid1 s0 v1 s1 evs ->
      exists s0',
      atomic_exec op_step ap tid1 s v1 s0' evs /\
      op_step opMover tid0 s0' v0 s1.
  Proof.
    intros.
    generalize dependent s.
    induction H2; intros; eauto.
    - edestruct IHatomic_exec1; eauto.
      edestruct IHatomic_exec2; intuition eauto.
    - edestruct H; intuition eauto.
    - edestruct IHatomic_exec; intuition eauto.
  Qed.

  Lemma atomic_exec_left_mover : forall tid0 tid1 s s0 `(ap : proc opT opHiT T) s1 v1 evs v0,
    left_mover ->
    tid0 <> tid1 ->
    atomic_exec op_step ap tid1 s v1 s0 evs ->
    op_step opMover tid0 s0 v0 s1 ->
      exists s0',
      op_step opMover tid0 s v0 s0' /\
      atomic_exec op_step ap tid1 s0' v1 s1 evs.
  Proof.
    intros.
    generalize dependent s1.
    induction H1; intros; eauto.
    - edestruct IHatomic_exec2; eauto.
      edestruct IHatomic_exec1; intuition eauto.
    - edestruct H.
      edestruct H4.
      3: eauto.
      2: eauto.
      eauto.
      intuition eauto.
    - edestruct IHatomic_exec; intuition eauto.
  Qed.

  Lemma exec_tid_right_mover : forall tid0 tid1 s s0 `(p : proc opT opHiT T) s1 result' evs v0,
    right_mover ->
    tid0 <> tid1 ->
    op_step opMover tid0 s v0 s0 ->
    exec_tid op_step tid1 s0 p s1 result' evs ->
      exists s0',
      exec_tid op_step tid1 s p s0' result' evs /\
      op_step opMover tid0 s0' v0 s1.
  Proof.
    intros.
    induction H2; simpl; eauto.
    - edestruct H; intuition eauto.
    - edestruct atomic_exec_right_mover; intuition eauto.
    - edestruct IHexec_tid; intuition eauto.
  Qed.

  Lemma exec_tid_left_mover : forall tid0 tid1 s s0 `(p : proc opT opHiT T) s1 result' evs v0,
    left_mover ->
    tid0 <> tid1 ->
    exec_tid op_step tid1 s p s0 result' evs ->
    op_step opMover tid0 s0 v0 s1 ->
      exists s0',
      op_step opMover tid0 s v0 s0' /\
      exec_tid op_step tid1 s0' p s1 result' evs.
  Proof.
    intros.
    induction H1; simpl; eauto.
    - edestruct H.
      edestruct H4.
      3: eauto.
      2: eauto.
      eauto.
      intuition eauto.
    - edestruct atomic_exec_left_mover; intuition eauto.
    - edestruct IHexec_tid; intuition eauto.
  Qed.

  Lemma exec_left_mover : forall s ts tid `(rx : _ -> proc opT opHiT T) tr,
    left_mover ->
    exec_prefix op_step s ts [[ tid := Proc (x <- OpExec opMover; rx x) ]] tr ->
    exists s' r,
      op_step opMover tid s r s' /\
      exec_prefix op_step s' ts [[ tid := Proc (rx r) ]] tr.
  Proof.
    intros.

    match goal with
    | H : exec_prefix _ _ (thread_upd ?ts ?tid ?p) _ |- _ =>
      remember (thread_upd ts tid p);
      generalize dependent ts;
      unfold exec_prefix in H; repeat deex;
      induction H; intros; subst
    end.

    - destruct (tid == tid0); subst.
      + autorewrite with t in *.
        repeat maybe_proc_inv.
        repeat exec_tid_inv.
        do 2 eexists; intuition eauto.

      + autorewrite with t in *.

        edestruct IHexec; intuition idtac.
        rewrite thread_upd_upd_ne; eauto.
        repeat deex.

        eapply exec_tid_left_mover in H1; eauto.
        repeat deex.

        do 2 eexists; intuition eauto.

        eapply ExecPrefixOne with (tid := tid0).
          autorewrite with t; eauto.
          eauto.
          rewrite thread_upd_upd_ne; eauto.

    - destruct H.
      edestruct H; repeat deex.
      do 2 eexists; split.
      eauto.
      eauto.
  Qed.

  Theorem hitrace_incl_atomize_opexec_right_mover :
    right_mover ->
    forall `(p : _ -> proc opT opHiT TP)
           `(rx : _ -> proc opT opHiT TF),
    hitrace_incl op_step
      (Bind (Bind (OpExec opMover) (fun r => (Atomic (p r)))) rx)
      (Bind (Atomic (Bind (OpExec opMover) p)) rx).
  Proof.
    intros.
    eapply hitrace_incl_proof_helper; intros.
    repeat exec_tid_inv.

    match goal with
    | H : exec_prefix _ _ (thread_upd ?ts ?tid ?pp) _ |- _ =>
      remember (thread_upd ts tid pp);
      generalize dependent ts;
      generalize dependent s;
      destruct H as [? H];
      induction H; simpl; intros; subst; eauto
    end.

    destruct (tid == tid0); subst.
    + autorewrite with t in *.
      repeat maybe_proc_inv.
      repeat exec_tid_inv.

      eexists; split.
      eapply ExecPrefixOne with (tid := tid0).
        autorewrite with t in *; eauto.
        eauto.
        simpl. autorewrite with t. eauto.
      simpl; eauto.

    + autorewrite with t in *.
      edestruct exec_tid_right_mover; intuition eauto.
      edestruct IHexec; eauto.
        rewrite thread_upd_upd_ne; eauto.
      intuition idtac.

      eexists; split.
      eapply ExecPrefixOne with (tid := tid0).
        autorewrite with t; eauto.
        eauto.
        rewrite thread_upd_upd_ne; eauto.
      eauto.
  Qed.

  Theorem hitrace_incl_atomize_op_right_mover :
    right_mover ->
    forall `(p : _ -> proc opT opHiT TP)
           `(rx : _ -> proc opT opHiT TF),
    hitrace_incl op_step
      (Bind (Bind (Op opMover) (fun r => (Atomic (p r)))) rx)
      (Bind (Atomic (Bind (Op opMover) p)) rx).
  Proof.
    unfold Op; intros.

    repeat rewrite exec_equiv_bind_bind.
    rewrite atomic_equiv_bind_bind with (p1 := OpCall _).
    rewrite <- hitrace_incl_atomize_opcall.
    rewrite exec_equiv_bind_bind with (p1 := OpCall _).
    eapply hitrace_incl_bind_a; intros.

    repeat rewrite exec_equiv_bind_bind.
    rewrite atomic_equiv_bind_bind with (p1 := OpExec _).
    rewrite <- hitrace_incl_atomize_opexec_right_mover by eauto.
    rewrite exec_equiv_bind_bind with (p1 := OpExec _).
    eapply hitrace_incl_bind_a; intros.

    repeat rewrite exec_equiv_bind_bind.
    rewrite <- hitrace_incl_atomize_opret.
    rewrite exec_equiv_bind_bind with (p1 := OpRet _).
    eapply hitrace_incl_bind_a; intros.

    reflexivity.
  Qed.

  Theorem hitrace_incl_atomize_opexec_left_mover :
    left_mover ->
    forall `(p : proc opT opHiT TP)
           `(rx : _ -> proc opT opHiT TF),
    hitrace_incl op_step
      (Bind (Bind (Atomic p) (fun _ => OpExec opMover)) rx)
      (Bind (Atomic (Bind p (fun _ => OpExec opMover))) rx).
  Proof.
    intros.
    eapply hitrace_incl_proof_helper; intros.
    repeat exec_tid_inv.
    eapply exec_left_mover in H1; eauto.
    repeat deex.

    eexists; split.
    eapply ExecPrefixOne with (tid := tid).
      autorewrite with t; eauto.
      eauto.
      autorewrite with t. eauto.
    rewrite app_nil_r; eauto.
  Qed.

  Theorem hitrace_incl_atomize_opexec_ret_left_mover :
    left_mover ->
    forall `(p : proc opT opHiT TP)
           `(f : TP -> _ -> TR)
           `(rx : _ -> proc opT opHiT TF),
    hitrace_incl op_step
      (Bind (Bind (Atomic p) (fun a => Bind (OpExec opMover) (fun b => Ret (f a b)))) rx)
      (Bind (Atomic (Bind p (fun a => Bind (OpExec opMover) (fun b => Ret (f a b))))) rx).
  Proof.
    intros.
    eapply hitrace_incl_proof_helper; intros.
    repeat exec_tid_inv.
    rewrite exec_equiv_bind_bind in H1.
    eapply exec_left_mover in H1; eauto.
    repeat deex.

    eapply hitrace_incl_ts_proof_helper in H1.
    repeat deex.

    eexists; split.
    eapply ExecPrefixOne with (tid := tid).
      autorewrite with t; eauto.
      eauto 10.
      autorewrite with t. eauto.
    rewrite app_nil_r; eauto.

    intros.
    repeat exec_tid_inv.
    eauto.
  Qed.

  Theorem hitrace_incl_atomize_op_ret_left_mover :
    left_mover ->
    forall `(p : proc opT opHiT TP)
           `(f : TP -> _ -> TR)
           `(rx : _ -> proc opT opHiT TF),
    hitrace_incl op_step
      (Bind (Bind (Atomic p) (fun a => Bind (Op opMover) (fun b => Ret (f a b)))) rx)
      (Bind (Atomic (Bind p (fun a => Bind (Op opMover) (fun b => Ret (f a b))))) rx).
  Proof.
    unfold Op; intros.

    etransitivity.
    2: setoid_rewrite atomic_equiv_bind_bind with (p1 := OpCall _).
    2: setoid_rewrite atomic_equiv_bind_bind'.
    2: setoid_rewrite atomic_equiv_bind_bind with (p1 := OpExec _).
    2: setoid_rewrite atomic_equiv_bind_bind'.
    reflexivity.

    rewrite <- hitrace_incl_atomize_opret_ret_l.

    repeat rewrite exec_equiv_bind_bind.
    rewrite <- hitrace_incl_atomize_opexec_ret_left_mover by eauto.

    repeat rewrite exec_equiv_bind_bind.
    rewrite <- hitrace_incl_atomize_opcall_ret_l.

    repeat rewrite exec_equiv_bind_bind.
    eapply hitrace_incl_bind_a; intros.

    repeat rewrite exec_equiv_bind_bind with (p1 := OpCall _).
    eapply hitrace_incl_bind_a; intros.

    rewrite exec_equiv_ret_bind.
    repeat rewrite exec_equiv_bind_bind with (p1 := OpExec _).
    eapply hitrace_incl_bind_a; intros.

    rewrite exec_equiv_ret_bind.
    repeat rewrite exec_equiv_bind_bind with (p1 := OpRet _).
    eapply hitrace_incl_bind_a; intros.

    rewrite exec_equiv_ret_bind.
    rewrite exec_equiv_ret_bind.
    simpl.
    reflexivity.
  Qed.

End Movers.

Hint Resolve both_mover_left.
Hint Resolve both_mover_right.

Arguments left_mover {opT State} op_step {moverT}.
Arguments right_mover {opT State} op_step {moverT}.
Arguments both_mover {opT State} op_step {moverT}.


Section YSA.

  Variable opT : Type -> Type.
  Variable opHiT : Type -> Type.
  Variable State : Type.
  Variable op_step : OpSemantics opT State.

  (** Something similar to the Yield Sufficiency Automaton from the GC paper *)

  Inductive left_movers : forall T, proc opT opHiT T -> Prop :=
  | LeftMoversOne :
    forall `(opMover : opT oT) `(rx : _ -> proc _ _ T),
    left_mover op_step opMover ->
    (forall a, left_movers (rx a)) ->
    left_movers (Bind (Op opMover) rx)
  | LeftMoversRet :
    forall `(v : T),
    left_movers (Ret v).

  Inductive at_most_one_non_mover : forall T, proc opT opHiT T -> Prop :=
  | ZeroNonMovers :
    forall `(p : proc _ _ T),
    left_movers p ->
    at_most_one_non_mover p
  | OneNonMover :
    forall `(op : opT T) `(rx : _ -> proc _ _ R),
    (forall a, left_movers (rx a)) ->
    at_most_one_non_mover (Bind (Op op) rx).

  Inductive ysa_movers : forall T, proc opT opHiT T -> Prop :=
  | RightMoversOne :
    forall `(opMover : opT oT) `(rx : _ -> proc _ _ T),
    right_mover op_step opMover ->
    (forall a, ysa_movers (rx a)) ->
    ysa_movers (Bind (Op opMover) rx)
  | RightMoversDone :
    forall `(p : proc _ _ T),
    at_most_one_non_mover p ->
    ysa_movers p.

  Lemma exec_OpCall : forall s ts tid `(opMover : opT oT) `(rx : _ -> proc opT opHiT T) tr,
    exec_prefix op_step s ts [[ tid := Proc (x <- OpCall opMover; rx x) ]] tr ->
    exists tr',
      exec_prefix op_step s ts [[ tid := Proc (rx tt) ]] tr' /\
      trace_match_hi tr tr'.
  Proof.
    intros.

    match goal with
    | H : exec_prefix _ _ (thread_upd ?ts ?tid ?p) ?t |- _ =>
      remember (thread_upd ts tid p);
      remember t;
      generalize dependent ts;
      generalize dependent tr;
      destruct H as [? H];
      induction H; intros; subst
    end.

    - destruct (tid == tid0); subst; autorewrite with t in *.
      + repeat maybe_proc_inv.
        repeat exec_tid_inv.
        simpl; eauto.

      + edestruct IHexec.
          autorewrite with t; eauto.
          rewrite thread_upd_upd_ne; eauto.
        intuition idtac.

        eexists; split.
        eapply ExecPrefixOne with (tid := tid0).
          autorewrite with t; eauto.
          eauto.
          rewrite thread_upd_upd_ne; eauto.

        eauto.

    - eauto.
  Qed.

  Lemma exec_OpRet : forall s ts tid `(v : oT) `(rx : _ -> proc opT opHiT T) tr,
    exec_prefix op_step s ts [[ tid := Proc (x <- OpRet v; rx x) ]] tr ->
    exists tr',
      exec_prefix op_step s ts [[ tid := Proc (rx v) ]] tr' /\
      trace_match_hi tr tr'.
  Proof.
    intros.

    match goal with
    | H : exec_prefix _ _ (thread_upd ?ts ?tid ?p) ?t |- _ =>
      remember (thread_upd ts tid p);
      remember t;
      generalize dependent ts;
      generalize dependent tr;
      destruct H as [? H];
      induction H; intros; subst
    end.

    - destruct (tid == tid0); subst; autorewrite with t in *.
      + repeat maybe_proc_inv.
        repeat exec_tid_inv.
        simpl; eauto.

      + edestruct IHexec.
          autorewrite with t; eauto.
          rewrite thread_upd_upd_ne; eauto.
        intuition idtac.

        eexists; split.
        eapply ExecPrefixOne with (tid := tid0).
          autorewrite with t; eauto.
          eauto.
          rewrite thread_upd_upd_ne; eauto.

        eauto.

    - eauto.
  Qed.

  Theorem hitrace_incl_atomize_ysa_left_movers :
    forall T L R (p : proc _ _ T) (l : _ -> proc _ _ L) (rx : _ -> proc _ _ R),
      (forall a, left_movers (l a)) ->
      hitrace_incl op_step
        (Bind (Bind (Atomic p) l) rx)
        (Bind (Atomic (Bind p l)) rx).
  Proof.
    intros.
    eapply hitrace_incl_proof_helper; intros.
    repeat exec_tid_inv.

    cut (exists tr' v1 s1 evs1,
      atomic_exec op_step (l v) tid s' v1 s1 evs1 /\
      exec_prefix op_step s1 ts [[ tid := Proc (rx v1) ]] tr' /\
      trace_match_hi tr (prepend tid evs1 tr')); intros.
    {
      repeat deex.
      eexists; split.

      eapply ExecPrefixOne with (tid := tid).
        autorewrite with t; eauto.
        eauto.
        autorewrite with t; eauto.
      rewrite prepend_app.
      eauto.
    }

    specialize (H v); remember (l v).
    generalize dependent p.
    generalize dependent l.
    generalize dependent T.
    generalize dependent s'.
    generalize dependent tr.
    generalize dependent evs.
    induction H; intros.

    - unfold Op in H2.
      repeat rewrite exec_equiv_bind_bind in H2.
      eapply exec_OpCall in H2; repeat deex.
      repeat rewrite exec_equiv_bind_bind in H2.
      eapply exec_left_mover in H2; eauto; repeat deex.
      repeat rewrite exec_equiv_bind_bind in H4.
      eapply exec_OpRet in H4; repeat deex.

      edestruct H1 with (p := Bind p (fun _ => Op opMover)).
      eassumption.
      reflexivity.
      eauto.

      repeat deex.
      do 4 eexists; intuition idtac.

      eauto.
      eauto.
      rewrite app_nil_l in *.

      unfold trace_match_hi; simpl.
      congruence.

    - rewrite exec_equiv_ret_bind in H1.
      do 4 eexists; intuition idtac.
      eauto.
      eauto.
      eauto.
  Qed.

  Theorem hitrace_incl_atomize_ysa :
    forall T R (p : proc _ _ T) (rx : _ -> proc _ _ R),
      ysa_movers p ->
      hitrace_incl op_step
        (Bind p rx)
        (Bind (Atomic p) rx).
  Proof.
    intros.
    induction H.
    {
      rewrite <- hitrace_incl_atomize_op_right_mover by eauto.
      repeat rewrite exec_equiv_bind_bind.
      eapply hitrace_incl_bind_a; intros.
      eauto.
    }

    inversion H; clear H; repeat sigT_eq.
    - rewrite <- exec_equiv_ret_bind with (v := tt) (p0 := (fun _ => p)) at 1.
      rewrite <- atomic_equiv_ret_bind with (v := tt) (p0 := (fun _ => p)).
      erewrite <- hitrace_incl_atomize_ysa_left_movers; eauto.
      rewrite exec_equiv_atomicret_ret.
      reflexivity.
    - erewrite <- hitrace_incl_atomize_ysa_left_movers; eauto.
      repeat rewrite exec_equiv_bind_bind.
      rewrite hitrace_incl_op.
      reflexivity.
  Qed.

End YSA.

Hint Constructors ysa_movers.
Hint Constructors at_most_one_non_mover.
Hint Constructors left_movers.


Ltac destruct_ifs :=
  repeat match goal with
  | |- context[if ?a == ?b then _ else _] =>
    destruct (a == b)
  end.

Section PerThreadState.

  Variable opT : Type -> Type.
  Variable opHiT : Type -> Type.
  Variable ThreadState : Type.
  Definition State := forall (tid : nat), ThreadState.
  Variable op_step : OpSemantics opT State.

  Definition state_upd (s : State) (tid : nat) (val : ThreadState) :=
    fun tid' =>
      if tid' == tid then val else s tid'.

  Theorem state_upd_upd_ne : forall tid1 v1 tid2 v2 s, tid1 <> tid2 ->
    state_upd (state_upd s tid1 v1) tid2 v2 =
    state_upd (state_upd s tid2 v2) tid1 v1.
  Proof.
    intros; apply functional_extensionality; intros.
    unfold state_upd.
      destruct_ifs; congruence.
  Qed.

  Theorem state_upd_upd_eq : forall tid v1 v2 s,
    state_upd (state_upd s tid v1) tid v2 =
    state_upd s tid v2.
  Proof.
    intros; apply functional_extensionality; intros.
    unfold state_upd.
      destruct_ifs; congruence.
  Qed.

  Theorem state_upd_eq : forall tid v1 s,
    state_upd s tid v1 tid = v1.
  Proof.
    intros; unfold state_upd; destruct_ifs; congruence.
  Qed.

  Theorem state_upd_ne : forall tid1 v1 tid2 s, tid1 <> tid2 ->
    state_upd s tid1 v1 tid2 = s tid2.
  Proof.
    intros; unfold state_upd; destruct_ifs; congruence.
  Qed.

End PerThreadState.
