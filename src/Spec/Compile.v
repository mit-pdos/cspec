Require Import ConcurProc.
Require Import Equiv.
Require Import Helpers.Helpers.
Require Import FunctionalExtensionality.

Global Set Implicit Arguments.
Global Generalizable All Variables.


Section Compiler.

  Variable opLoT : Type -> Type.
  Variable opMidT : Type -> Type.
  Variable opHiT : Type -> Type.

  Variable compile_op : forall T, opMidT T -> proc opLoT opMidT T.

  Definition atomize {T} (op : opMidT T) : proc opLoT opMidT T :=
    Atomic (compile_op op).

  Definition hicall T (op : opMidT T) : proc opLoT opMidT T :=
    _ <- OpCallHi op;
    r <- compile_op op;
    OpRetHi r.

  Inductive compile_ok : forall T (p1 : proc opLoT opMidT T) (p2 : proc opMidT opHiT T), Prop :=
  | CompileOpcode : forall `(op : opMidT T),
    compile_ok (hicall op) (Op op)
  | CompileRet : forall `(x : T),
    compile_ok (Ret x) (Ret x)
  | CompileBind : forall `(p1a : proc opLoT opMidT T1) (p2a : proc opMidT opHiT T1)
                         `(p1b : T1 -> proc _ _ T2) (p2b : T1 -> proc _ _ T2),
    compile_ok p1a p2a ->
    (forall x, compile_ok (p1b x) (p2b x)) ->
    compile_ok (Bind p1a p1b) (Bind p2a p2b)
  | CompileOpCallHi : forall `(op : opHiT T),
    compile_ok (Ret tt) (OpCallHi op)
  | CompileOpRetHi : forall `(v : T),
    compile_ok (Ret v) (OpRetHi v).

  Fixpoint compile T (p : proc opMidT opHiT T) : proc opLoT opMidT T :=
    match p with
    | Ret t => Ret t
    | OpCall op => OpCallHi op
    | OpExec op => compile_op op
    | OpRet r => OpRetHi r
    | Bind p1 p2 => Bind (compile p1) (fun r => compile (p2 r))
    | OpCallHi _ => Ret tt
    | OpRetHi v => Ret v
    | Atomic p => Atomic (compile p)
    end.

End Compiler.

Arguments hicall {opLoT opMidT} compile_op {T}.

Hint Constructors compile_ok.


Ltac destruct_ifs :=
  repeat match goal with
  | |- context[if ?a == ?b then _ else _] =>
    destruct (a == b)
  end.

Section Disjoint.

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


  Definition disjoint_writes := forall T (op : opT T) tid s v s',
    op_step op tid s v s' ->
    forall tid0,
      tid0 <> tid ->
      s tid0 = s' tid0.

  Definition disjoint_reads := forall T (op : opT T) tid s v s',
    op_step op tid s v s' ->
    forall tid0 x,
    tid0 <> tid ->
    op_step op tid
      (state_upd s tid0 x)
      v
      (state_upd s' tid0 x).

  Variable disjoint_w : disjoint_writes.
  Variable disjoint_r : disjoint_reads.

  Lemma exec_tid_disjoint_writes : forall T tid0 s p s' result' evs,
    @exec_tid opT opHiT State op_step T tid0 s p s' result' evs ->
    forall tid1,
      tid0 <> tid1 ->
      s tid1 = s' tid1.
  Proof.
    intros.
    induction H; eauto.
    induction H; eauto.
    + eapply eq_trans.
      apply IHatomic_exec1; eauto.
      apply IHatomic_exec2; eauto.
  Qed.

  Lemma exec_tid_disjoint_reads : forall tid0 v tid1 T s p s' result' evs,
    tid0 <> tid1 ->
    @exec_tid opT opHiT State op_step T tid1 s p s' result' evs ->
    @exec_tid opT opHiT State op_step T tid1 (state_upd s tid0 v) p (state_upd s' tid0 v) result' evs.
  Proof.
    intros.
    induction H0; simpl; eauto.
    constructor.
    induction H0; eauto.
  Qed.

  Theorem hitrace_incl_atomic_start :
    forall `(ap : proc opT opHiT TA)
           `(p1 : proc _ _ T')
            (p2 : _ -> proc _ _ T'),
    (forall s tid,
      exists r s' evs,
      atomic_exec op_step ap tid s r s' evs /\
      (forall tr1 tr2, trace_match_hi tr1 tr2 ->
                       trace_match_hi tr1 (prepend tid evs tr2)) /\
      hitrace_incl_s s s' tid op_step
        p1 (p2 r)) ->
    hitrace_incl op_step
      p1
      (Bind (Atomic ap) p2).
  Proof.
    unfold hitrace_incl, hitrace_incl_opt,
           hitrace_incl_ts, hitrace_incl_ts_s; intros.

    edestruct H; repeat deex.
    edestruct H3; eauto; repeat deex.
    intuition idtac.

    eexists; split.
    eapply ExecOne with (tid := tid).
      autorewrite with t; eauto.
      eauto 20.
      simpl. autorewrite with t. eauto.
    eauto.
  Qed.

End Disjoint.
