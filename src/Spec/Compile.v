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


Section Commutes.

  Variable opT : Type -> Type.
  Variable opHiT : Type -> Type.
  Variable State : Type.
  Variable op_step : OpSemantics opT State.

  Definition step_commutes :=
    forall `(op0 : opT T1) `(op1 : opT T2) tid0 tid1 s s0 s1 v0 v1,
      tid0 <> tid1 ->
      op_step op0 tid0 s v0 s0 ->
      op_step op1 tid1 s0 v1 s1 ->
      exists s',
        op_step op1 tid1 s v1 s' /\
        op_step op0 tid0 s' v0 s1.

  Variable commutes : step_commutes.

  Lemma atomic_exec_commutes : forall tid0 tid1 s s0 `(ap : proc opT opHiT T) s1 v1 evs `(op : opT T') v0,
    tid0 <> tid1 ->
    op_step op tid0 s v0 s0 ->
    atomic_exec op_step ap tid1 s0 v1 s1 evs ->
      exists s0',
      atomic_exec op_step ap tid1 s v1 s0' evs /\
      op_step op tid0 s0' v0 s1.
  Proof.
    intros.
    generalize dependent s.
    induction H1; intros; eauto.
    - edestruct IHatomic_exec1; eauto.
      edestruct IHatomic_exec2; intuition eauto.
    - edestruct commutes; intuition eauto.
    - edestruct IHatomic_exec; intuition eauto.
  Qed.

  Lemma exec_tid_commutes : forall tid0 tid1 s s0 `(p : proc opT opHiT T) s1 result' evs `(op : opT T') v0,
    tid0 <> tid1 ->
    op_step op tid0 s v0 s0 ->
    exec_tid op_step tid1 s0 p s1 result' evs ->
      exists s0',
      exec_tid op_step tid1 s p s0' result' evs /\
      op_step op tid0 s0' v0 s1.
  Proof.
    intros.
    induction H1; simpl; eauto.
    - edestruct commutes; intuition eauto.
    - edestruct atomic_exec_commutes; intuition eauto.
    - edestruct IHexec_tid; intuition eauto.
  Qed.

  Theorem hitrace_incl_atomize_opexec :
    forall `(op : opT T)
           `(p : _ -> proc opT opHiT TP)
           `(rx : _ -> proc opT opHiT TF),
    hitrace_incl op_step
      (Bind (Bind (OpExec op) (fun r => (Atomic (p r)))) rx)
      (Bind (Atomic (Bind (OpExec op) p)) rx).
  Proof.
    intros.
    eapply hitrace_incl_proof_helper; intros.
    repeat exec_tid_inv.

    match goal with
    | H : exec _ _ (thread_upd ?ts ?tid ?pp) _ |- _ =>
      remember (thread_upd ts tid pp);
      generalize dependent ts;
      generalize dependent s;
      induction H; simpl; intros; subst
    end.

    - destruct (tid == tid0); subst.
      + autorewrite with t in *.
        repeat maybe_proc_inv.
        repeat exec_tid_inv.

        eexists; split.
        eapply ExecOne with (tid := tid0).
          autorewrite with t in *; eauto.
          eauto.
          simpl. autorewrite with t. eauto.
        simpl; eauto.

      + autorewrite with t in *.
        edestruct exec_tid_commutes; intuition eauto.
        edestruct IHexec; eauto.
          rewrite thread_upd_upd_ne; eauto.
        intuition idtac.

        eexists; split.
        eapply ExecOne with (tid := tid0).
          autorewrite with t; eauto.
          eauto.
          rewrite thread_upd_upd_ne; eauto.
        eauto.

    - exfalso; eauto.
  Qed.

End Commutes.


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
