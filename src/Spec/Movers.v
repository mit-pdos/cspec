Require Import ConcurProc.
Require Import Equiv.
Require Import Helpers.Helpers.
Require Import FunctionalExtensionality.
Require Import Omega.
Require Import List.

Import ListNotations.

Global Set Implicit Arguments.
Global Generalizable All Variables.


Section Movers.

  Variable opT : Type -> Type.
  Variable State : Type.
  Variable op_step : OpSemantics opT State.

  Variable moverT : Type.
  Variable opMover : opT moverT.

  Definition enabled_in (tid : nat) (s : State) :=
    exists rM sM,
      op_step opMover tid s rM sM.

  Definition always_enabled :=
    forall tid s,
      enabled_in tid s.

  Definition enabled_after `(p : proc opT T) :=
    forall tid s v s' evs,
      atomic_exec op_step p tid s v s' evs ->
      enabled_in tid s'.

  Definition enabled_stable :=
    forall tid tid' s `(op : opT T) r s',
      tid <> tid' ->
      enabled_in tid s ->
      op_step op tid' s r s' ->
      enabled_in tid s'.

  Lemma always_enabled_to_stable :
    always_enabled -> enabled_stable.
  Proof.
    firstorder.
  Qed.

  Definition right_mover :=
    forall `(op1 : opT T2) tid0 tid1 s s0 s1 v0 v1,
      tid0 <> tid1 ->
      op_step opMover tid0 s v0 s0 ->
      op_step op1 tid1 s0 v1 s1 ->
      exists s',
        op_step op1 tid1 s v1 s' /\
        op_step opMover tid0 s' v0 s1.

  Definition left_mover :=
    enabled_stable /\
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


  Lemma atomic_exec_right_mover : forall tid0 tid1 s s0 `(ap : proc opT T) s1 v1 evs v0,
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
    - edestruct IHatomic_exec; intuition eauto.
  Qed.

  Lemma atomic_exec_left_mover : forall tid0 tid1 s s0 `(ap : proc opT T) s1 v1 evs v0,
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
    - edestruct IHatomic_exec; intuition eauto.
  Qed.

  Lemma exec_tid_right_mover : forall tid0 tid1 s s0 `(p : proc opT T) s1 result' evs v0,
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

  Lemma exec_tid_left_mover : forall tid0 tid1 s s0 `(p : proc opT T) s1 result' evs v0,
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

  Lemma enabled_stable_atomic_exec :
    enabled_stable ->
    forall tid tid' s `(p : proc opT T) r s' evs,
      tid <> tid' ->
      enabled_in tid s ->
      atomic_exec op_step p tid' s r s' evs ->
      enabled_in tid s'.
  Proof.
    intros.
    induction H2; eauto.
  Qed.

  Hint Resolve enabled_stable_atomic_exec.

  Lemma enabled_stable_exec_tid :
    enabled_stable ->
    forall tid tid' s `(p : proc opT T) r s' evs,
      tid <> tid' ->
      enabled_in tid s ->
      exec_tid op_step tid' s p s' r evs ->
      enabled_in tid s'.
  Proof.
    intros.
    induction H2; eauto.
  Qed.

  Hint Resolve enabled_stable_exec_tid.

  Lemma exec_left_mover : forall s ts tid `(rx : _ -> proc opT T) tr,
    left_mover ->
    enabled_in tid s ->
    exec_prefix op_step s ts [[ tid := Proc (x <- Op opMover; rx x) ]] tr ->
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
          eapply enabled_stable_exec_tid; eauto.
          destruct H; eauto.
        rewrite thread_upd_upd_ne; eauto.
        repeat deex.

        eapply exec_tid_left_mover in H2; eauto.
        repeat deex.

        do 2 eexists; intuition eauto.

        eapply ExecPrefixOne with (tid := tid0).
          autorewrite with t; eauto.
          eauto.
          rewrite thread_upd_upd_ne; eauto.

    - edestruct H0; repeat deex.
      do 2 eexists; split.
      eauto.
      eauto.
  Qed.

  Theorem trace_incl_atomize_op_right_mover :
    right_mover ->
    forall `(p : _ -> proc opT TP)
           `(rx : _ -> proc opT TF),
    trace_incl op_step
      (Bind (Bind (Op opMover) (fun r => (Atomic (p r)))) rx)
      (Bind (Atomic (Bind (Op opMover) p)) rx).
  Proof.
    intros.
    eapply trace_incl_proof_helper; intros.
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

  Theorem trace_incl_atomize_op_left_mover :
    forall `(p : proc opT TP)
           `(rx : _ -> proc opT TF),
    left_mover ->
    enabled_after p ->
    trace_incl op_step
      (Bind (Bind (Atomic p) (fun _ => Op opMover)) rx)
      (Bind (Atomic (Bind p (fun _ => Op opMover))) rx).
  Proof.
    intros.
    eapply trace_incl_proof_helper; intros.
    repeat exec_tid_inv.
    eapply exec_left_mover in H2; eauto.
    repeat deex.

    eexists; split.
    eapply ExecPrefixOne with (tid := tid).
      autorewrite with t; eauto.
      eauto.
      autorewrite with t. eauto.
    rewrite app_nil_r; eauto.
  Qed.

  Theorem trace_incl_atomize_op_ret_left_mover :
    forall `(p : proc opT TP)
           `(f : TP -> _ -> TR)
           `(rx : _ -> proc opT TF),
    left_mover ->
    enabled_after p ->
    trace_incl op_step
      (Bind (Bind (Atomic p) (fun a => Bind (Op opMover) (fun b => Ret (f a b)))) rx)
      (Bind (Atomic (Bind p (fun a => Bind (Op opMover) (fun b => Ret (f a b))))) rx).
  Proof.
    intros.
    eapply trace_incl_proof_helper; intros.
    repeat exec_tid_inv.
    rewrite exec_equiv_bind_bind in H2.
    eapply exec_left_mover in H2; eauto.
    repeat deex.

    eapply trace_incl_ts_proof_helper in H2.
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

End Movers.

Hint Resolve both_mover_left.
Hint Resolve both_mover_right.
Hint Resolve always_enabled_to_stable.

Arguments left_mover {opT State} op_step {moverT}.
Arguments right_mover {opT State} op_step {moverT}.
Arguments both_mover {opT State} op_step {moverT}.
Arguments enabled_after {opT State} op_step {moverT} opMover {T} p.
Arguments enabled_in {opT State} op_step {moverT}.
Arguments always_enabled {opT State} op_step {moverT}.


Section YSA.

  Variable opT : Type -> Type.
  Variable State : Type.
  Variable op_step : OpSemantics opT State.

  (** Something similar to the Yield Sufficiency Automaton from the GC paper *)

  Inductive left_movers : forall T, proc opT T -> Prop :=
  | LeftMoversOne :
    forall `(opMover : opT oT) `(rx : _ -> proc _ T),
    left_mover op_step opMover ->
    always_enabled op_step opMover ->
    (forall a, left_movers (rx a)) ->
    left_movers (Bind (Op opMover) rx)
  | LeftMoversRet :
    forall `(v : T),
    left_movers (Ret v).

  Inductive at_most_one_non_mover : forall T, proc opT T -> Prop :=
  | ZeroNonMovers :
    forall `(p : proc _ T),
    left_movers p ->
    at_most_one_non_mover p
  | OneNonMover :
    forall `(op : opT T) `(rx : _ -> proc _ R),
    (forall a, left_movers (rx a)) ->
    at_most_one_non_mover (Bind (Op op) rx).

  Inductive ysa_movers : forall T, proc opT T -> Prop :=
  | RightMoversOne :
    forall `(opMover : opT oT) `(rx : _ -> proc _ T),
    right_mover op_step opMover ->
    (forall a, ysa_movers (rx a)) ->
    ysa_movers (Bind (Op opMover) rx)
  | RightMoversDone :
    forall `(p : proc _ T),
    at_most_one_non_mover p ->
    ysa_movers p.

  Theorem trace_incl_atomize_ysa_left_movers :
    forall T L R (p : proc _ T) (l : _ -> proc _ L) (rx : _ -> proc _ R),
      (forall a, left_movers (l a)) ->
      trace_incl op_step
        (Bind (Bind (Atomic p) l) rx)
        (Bind (Atomic (Bind p l)) rx).
  Proof.
    intros.
    eapply trace_incl_proof_helper; intros.
    repeat exec_tid_inv.

    cut (exists tr' v1 s1 evs1,
      atomic_exec op_step (l v) tid s' v1 s1 evs1 /\
      exec_prefix op_step s1 ts [[ tid := Proc (rx v1) ]] tr' /\
      trace_eq tr (prepend tid evs1 tr')); intros.
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

    - repeat rewrite exec_equiv_bind_bind in H3.
      eapply exec_left_mover in H3; eauto; repeat deex.

      edestruct H2 with (p := Bind p (fun _ => Op opMover)).
      eassumption.
      reflexivity.
      eauto.

      repeat deex.
      do 4 eexists; intuition idtac.

      eauto.
      eauto.
      rewrite app_nil_l in *.
      eauto.

    - rewrite exec_equiv_ret_bind in H1.
      do 4 eexists; intuition idtac.
      eauto.
      eauto.
      eauto.
  Qed.

  Theorem trace_incl_atomize_ysa :
    forall T R (p : proc _ T) (rx : _ -> proc _ R),
      ysa_movers p ->
      trace_incl op_step
        (Bind p rx)
        (Bind (Atomic p) rx).
  Proof.
    intros.
    induction H.
    {
      rewrite <- trace_incl_atomize_op_right_mover by eauto.
      repeat rewrite exec_equiv_bind_bind.
      eapply trace_incl_bind_a; intros.
      eauto.
    }

    inversion H; clear H; repeat sigT_eq.
    - rewrite <- exec_equiv_ret_bind with (v := tt) (p0 := (fun _ => p)) at 1.
      rewrite <- atomic_equiv_ret_bind with (v := tt) (p0 := (fun _ => p)).
      erewrite <- trace_incl_atomize_ysa_left_movers; eauto.
      rewrite exec_equiv_atomicret_ret.
      reflexivity.
    - erewrite <- trace_incl_atomize_ysa_left_movers; eauto.
      repeat rewrite exec_equiv_bind_bind.
      rewrite trace_incl_op.
      reflexivity.
  Qed.

End YSA.

Hint Constructors ysa_movers.
Hint Constructors at_most_one_non_mover.
Hint Constructors left_movers.
