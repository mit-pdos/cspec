Require Import ConcurProc.
Require Import Equiv.
Require Import Helpers.Helpers.
Require Import FunctionalExtensionality.
Require Import Omega.

Global Set Implicit Arguments.
Global Generalizable All Variables.


Section Compiler.

  Variable opLoT : Type -> Type.
  Variable opMidT : Type -> Type.
  Variable opHiT : Type -> Type.

  Variable compile_op : forall T, opMidT T -> proc opLoT opMidT T.

  Definition atomize T (op : opMidT T) : proc opLoT opMidT T :=
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

  (* [atomic_compile_ok] is not quite [compile_ok] with [atomize]
     added to [compile_op].  It also breaks out [OpCallHi] and [OpRetHi]
     into separate matches, so that the [atomic_compile_ok] relation keeps
     holding across atomic steps taken by each thread.

     This means that [atomic_compile_ok] does not enforce the calling
     convention in itself: a program might have way too many [OpCallHi]s
     and not enough [OpRetHi]s, etc.
   *)
  Inductive atomic_compile_ok : forall T (p1 : proc opLoT opMidT T) (p2 : proc opMidT opHiT T), Prop :=
  | ACompileOpCall : forall `(op : opMidT T),
    atomic_compile_ok (OpCallHi op) (OpCall op)
  | ACompileOpExec : forall `(op : opMidT T),
    atomic_compile_ok (Atomic (compile_op op)) (OpExec op)
  | ACompileOpRet : forall `(v : T),
    atomic_compile_ok (OpRetHi v) (OpRet v)
  | ACompileRet : forall `(x : T),
    atomic_compile_ok (Ret x) (Ret x)
  | ACompileBind : forall `(p1a : proc opLoT opMidT T1) (p2a : proc opMidT opHiT T1)
                         `(p1b : T1 -> proc _ _ T2) (p2b : T1 -> proc _ _ T2),
    atomic_compile_ok p1a p2a ->
    (forall x, atomic_compile_ok (p1b x) (p2b x)) ->
    atomic_compile_ok (Bind p1a p1b) (Bind p2a p2b)
  | ACompileOpCallHi : forall `(op : opHiT T),
    atomic_compile_ok (Ret tt) (OpCallHi op)
  | ACompileOpRetHi : forall `(v : T),
    atomic_compile_ok (Ret v) (OpRetHi v).

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
Hint Constructors atomic_compile_ok.


Section Atomization.

  (* [atomize_ok] captures the notion that all implementations of opcodes
     in the left-side proc have been replaced with atomic-bracketed
     versions in the right-side proc. *)

  Variable opLoT : Type -> Type.
  Variable opHiT : Type -> Type.
  Variable compile_op : forall T, opHiT T -> proc opLoT opHiT T.

  Inductive atomize_ok : forall T (p1 p2 : proc opLoT opHiT T), Prop :=
  | AtomizeOpcode : forall `(op : opHiT T),
    atomize_ok (hicall compile_op op) (hicall (atomize compile_op) op)
  | AtomizeRet : forall `(x : T),
    atomize_ok (Ret x) (Ret x)
  | AtomizeBind : forall T1 T2 (p1a p2a : proc opLoT opHiT T1)
                               (p1b p2b : T1 -> proc opLoT opHiT T2),
    atomize_ok p1a p2a ->
    (forall x, atomize_ok (p1b x) (p2b x)) ->
    atomize_ok (Bind p1a p1b) (Bind p2a p2b).


  Variable State : Type.
  Variable op_step : OpSemantics opLoT State.

  Definition atomize_correct :=
    forall T (op : opHiT T)
           T' (p1rest p2rest : _ -> proc _ _ T'),
           (forall x, hitrace_incl op_step (p1rest x) (p2rest x)) ->
           hitrace_incl op_step
             (Bind (hicall compile_op op) p1rest)
             (Bind (hicall (atomize compile_op) op) p2rest).

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
    - eapply hitrace_incl_bind_a.
      eauto.
    - rewrite exec_equiv_bind_bind.
      rewrite exec_equiv_bind_bind.
      eapply IHatomize_ok.
      eauto.
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
