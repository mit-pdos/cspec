Require Import ConcurProc.
Require Import Equiv.
Require Import Helpers.Helpers.
Require Import FunctionalExtensionality.
Require Import Omega.
Require Import List.

Import ListNotations.

Global Set Implicit Arguments.
Global Generalizable All Variables.


Section StatePred.

  Variable opT : Type -> Type.
  Variable State : Type.
  Variable op_step : OpSemantics opT State.
  Variable P : forall (tid : nat) (s : State), Prop.

  Definition pred_stable :=
    forall tid tid' s s' `(op : opT T) r evs,
      P tid s ->
      tid' <> tid ->
      op_step op tid' s r s' evs ->
      P tid s'.

  Theorem pred_stable_atomic_exec :
    forall s0 s1 tid tid' `(p : proc _ T) r evs,
      pred_stable ->
      tid <> tid' ->
      P tid s0 ->
      atomic_exec op_step p tid' s0 r s1 evs ->
      P tid s1.
  Proof.
    intros.
    induction H2; eauto.
  Qed.

  Theorem pred_stable_exec_tid :
    forall s0 s1 tid tid' `(p : proc _ T) r evs,
      pred_stable ->
      tid <> tid' ->
      P tid s0 ->
      exec_tid op_step tid' s0 p s1 r evs ->
      P tid s1.
  Proof.
    intros.
    induction H2; eauto.
    eapply pred_stable_atomic_exec; eauto.
  Qed.

End StatePred.


Definition any {State} (tid : nat) (s : State) : Prop := True.

Theorem pred_stable_any : forall `(op_step : OpSemantics opT State),
  pred_stable op_step any.
Proof.
  firstorder.
Qed.

Theorem pred_stable_exec_any_others : forall `(op_step : OpSemantics opT State) `(p : proc _ T) P r,
  pred_stable op_step
    (fun tid s' => exists s s0,
      P tid s /\ exec_any op_step tid s p r s0 /\ exec_others op_step tid s0 s').
Proof.
  unfold pred_stable; intros; repeat deex.
  do 2 eexists; intuition eauto.
Qed.

Hint Resolve pred_stable_any.
Hint Resolve pred_stable_exec_any_others.


Section Movers.

  Variable opT : Type -> Type.
  Variable State : Type.
  Variable op_step : OpSemantics opT State.

  Variable moverT : Type.
  Variable opMover : opT moverT.

  Definition enabled_in (tid : nat) (s : State) :=
    exists rM sM evs,
      op_step opMover tid s rM sM evs.

  Definition always_enabled :=
    forall tid s,
      enabled_in tid s.

  Definition enabled_after `(p : proc opT T) :=
    forall tid s v s' evs,
      atomic_exec op_step p tid s v s' evs ->
      enabled_in tid s'.

  Definition enabled_stable :=
    forall tid tid' s `(op : opT T) r s' evs,
      tid <> tid' ->
      enabled_in tid s ->
      op_step op tid' s r s' evs ->
      enabled_in tid s'.

  Lemma always_enabled_to_stable :
    always_enabled -> enabled_stable.
  Proof.
    firstorder.
  Qed.

  Lemma always_enabled_to_enabled_in : forall tid s,
    always_enabled -> enabled_in tid s.
  Proof.
    firstorder.
  Qed.

  Definition right_mover :=
    forall tid0 s s0 v0 evs0,
      op_step opMover tid0 s v0 s0 evs0 ->
      evs0 = nil /\
      ( forall `(op1 : opT T2) tid1 s1 v1 evs1,
          tid0 <> tid1 ->
          op_step op1 tid1 s0 v1 s1 evs1 ->
          exists s',
            op_step op1 tid1 s v1 s' evs1 /\
            op_step opMover tid0 s' v0 s1 evs0 ).

  Definition left_mover :=
    enabled_stable /\
    forall tid1 s0 s1 v1 evs1,
      op_step opMover tid1 s0 v1 s1 evs1 ->
      evs1 = nil /\
      ( forall `(op0 : opT T0) tid0 s v0 evs0,
        tid0 <> tid1 ->
        op_step op0 tid0 s v0 s0 evs0 ->
        exists s',
          op_step opMover tid1 s v1 s' evs1 /\
          op_step op0 tid0 s' v0 s1 evs0 ).

  Definition left_mover_pred (P : nat -> State -> Prop) :=
    enabled_stable /\
    forall tid1 s0 s1 v1 evs1,
      op_step opMover tid1 s0 v1 s1 evs1 ->
      evs1 = nil /\
      ( forall `(op0 : opT T0) tid0 s v0 evs0,
        P tid1 s ->
        tid0 <> tid1 ->
        op_step op0 tid0 s v0 s0 evs0 ->
        exists s',
          op_step opMover tid1 s v1 s' evs1 /\
          op_step op0 tid0 s' v0 s1 evs0 ).

  Definition both_mover := right_mover /\ left_mover.

  Theorem both_mover_left : both_mover -> left_mover.
  Proof. unfold both_mover; intuition. Qed.

  Theorem both_mover_right : both_mover -> right_mover.
  Proof. unfold both_mover; intuition. Qed.

  Theorem left_mover_left_mover_pred :
    forall P, left_mover -> left_mover_pred P.
  Proof.
    unfold left_mover, left_mover_pred; intuition eauto.
    edestruct H1; eauto.
    edestruct H1; eauto.
  Qed.


  Theorem left_mover_pred_impl : forall (P1 P2 : nat -> State -> Prop),
    (forall tid s, P2 tid s -> P1 tid s) ->
    left_mover_pred P1 ->
    left_mover_pred P2.
  Proof.
    unfold left_mover_pred; intuition eauto.
    edestruct H2; eauto.
    edestruct H2; eauto.
  Qed.


  Lemma atomic_exec_right_mover : forall tid0 tid1 s s0 `(ap : proc opT T) s1 v1 evsM evs v0,
    right_mover ->
    tid0 <> tid1 ->
    op_step opMover tid0 s v0 s0 evsM ->
    atomic_exec op_step ap tid1 s0 v1 s1 evs ->
      exists s0',
        evsM = nil /\
        atomic_exec op_step ap tid1 s v1 s0' evs /\
        op_step opMover tid0 s0' v0 s1 evsM.
  Proof.
    intros.
    generalize dependent s.
    induction H2; intros; eauto.
    - edestruct H; eauto.
    - edestruct IHatomic_exec1; eauto.
      edestruct IHatomic_exec2; intuition eauto.
    - edestruct H; intuition eauto.
      edestruct H4; eauto.
      eexists; intuition eauto.
    - edestruct IHatomic_exec; intuition eauto.
  Qed.

  Lemma atomic_exec_left_mover : forall tid0 tid1 s s0 `(ap : proc opT T) s1 v1 evs evsM v0 P,
    left_mover_pred P ->
    pred_stable op_step P ->
    P tid0 s ->
    tid0 <> tid1 ->
    atomic_exec op_step ap tid1 s v1 s0 evs ->
    op_step opMover tid0 s0 v0 s1 evsM ->
    exists s0',
      evsM = nil /\
      op_step opMover tid0 s v0 s0' evsM /\
      atomic_exec op_step ap tid1 s0' v1 s1 evs.
  Proof.
    intros.
    generalize dependent s1.
    induction H3; intros; eauto.
    - edestruct H.
      edestruct H5; eauto.
    - edestruct IHatomic_exec2; eauto.
      eapply pred_stable_atomic_exec; eauto.
      edestruct IHatomic_exec1; intuition eauto.
    - edestruct H; clear H.
      edestruct H6; clear H6; eauto.
      edestruct H7.
      4: eauto.
      3: eauto.
      eauto.
      eauto.
      intuition eauto.
    - edestruct IHatomic_exec; intuition eauto.
  Qed.

  Lemma exec_tid_right_mover : forall tid0 tid1 s s0 `(p : proc opT T) s1 result' evs evsM v0,
    right_mover ->
    tid0 <> tid1 ->
    op_step opMover tid0 s v0 s0 evsM ->
    exec_tid op_step tid1 s0 p s1 result' evs ->
    exists s0',
      evsM = nil /\
      exec_tid op_step tid1 s p s0' result' evs /\
      op_step opMover tid0 s0' v0 s1 evsM.
  Proof.
    intros.
    induction H2; simpl; eauto.
    - edestruct H; eauto.
    - edestruct H; eauto.
      edestruct H4; intuition eauto.
    - edestruct atomic_exec_right_mover; intuition eauto.
    - edestruct IHexec_tid; intuition eauto.
    - edestruct H; eauto.
  Qed.

  Lemma exec_tid_left_mover : forall tid0 tid1 s s0 `(p : proc opT T) s1 result' evs evsM v0 P,
    left_mover_pred P ->
    pred_stable op_step P ->
    P tid0 s ->
    tid0 <> tid1 ->
    exec_tid op_step tid1 s p s0 result' evs ->
    op_step opMover tid0 s0 v0 s1 evsM ->
    exists s0',
      evsM = nil /\
      op_step opMover tid0 s v0 s0' evsM /\
      exec_tid op_step tid1 s0' p s1 result' evs.
  Proof.
    intros.
    induction H3; simpl; eauto.
    - edestruct H; eauto.
      edestruct H5; eauto.
    - edestruct H; clear H.
      edestruct H6; clear H6; eauto.
      edestruct H7.
      4: eauto.
      3: eauto.
      eauto.
      eauto.
      intuition eauto.
    - edestruct atomic_exec_left_mover; intuition eauto.
    - edestruct IHexec_tid; intuition eauto.
    - edestruct H; eauto.
      edestruct H5; eauto.
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

  Lemma exec_left_mover : forall s ts tid `(rx : _ -> proc opT T) tr P,
    left_mover_pred P ->
    pred_stable op_step P ->
    enabled_in tid s ->
    P tid s ->
    exec_prefix op_step s ts [[ tid := Proc (x <- Op opMover; rx x) ]] tr ->
    exists s' r,
      op_step opMover tid s r s' nil /\
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

        edestruct H; clear H; eauto.
        edestruct H4; clear H4; eauto.
        subst.
        do 2 eexists; intuition eauto.

      + autorewrite with t in *.

        edestruct IHexec; intuition idtac.
          eapply enabled_stable_exec_tid; eauto.
          destruct H; eauto.
          eapply pred_stable_exec_tid; eauto.
        rewrite thread_upd_ne_comm; eauto.
        repeat deex.

        eapply exec_tid_left_mover in H2; eauto.
        repeat deex.

        do 2 eexists; intuition eauto.

        eapply ExecPrefixOne with (tid := tid0).
          autorewrite with t; eauto.
          eauto.
          rewrite thread_upd_ne_comm; eauto.

    - edestruct H1; repeat deex.
      edestruct H; clear H; eauto.
      edestruct H5; clear H5; eauto.
      subst.
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

      abstract_tr.
      eapply ExecPrefixOne with (tid := tid0).
        autorewrite with t in *; eauto.
        eauto.
        simpl. autorewrite with t. eauto.
      rewrite prepend_app; auto.
    + autorewrite with t in *.
      edestruct exec_tid_right_mover; intuition eauto.
      edestruct IHexec; eauto.
        rewrite thread_upd_ne_comm; eauto.
      intuition idtac.

      abstract_tr.
      eapply ExecPrefixOne with (tid := tid0).
        autorewrite with t; eauto.
        eauto.
        rewrite thread_upd_ne_comm; eauto.
      subst; simpl; eauto.

    + edestruct H; eauto; subst; simpl; eauto.
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
    eapply exec_left_mover with (P := any) in H2; eauto.
    repeat deex.

    abstract_tr.
    eapply ExecPrefixOne with (tid := tid).
      autorewrite with t; eauto.
      eauto.
      autorewrite with t. eauto.
    rewrite app_nil_r; eauto.

    eapply left_mover_left_mover_pred; eauto.
    firstorder.
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
    eapply exec_left_mover with (P := any) in H2; eauto.
    repeat deex.

    eapply trace_incl_ts_s_proof_helper in H2.
    repeat deex.

    abstract_tr.
    eapply ExecPrefixOne with (tid := tid).
      autorewrite with t; eauto.
      eauto 10.
      autorewrite with t. eauto.
    rewrite app_nil_r; eauto.

    intros.
    repeat exec_tid_inv.
    eauto.

    eapply left_mover_left_mover_pred; eauto.
    firstorder.
  Qed.

End Movers.

Hint Resolve both_mover_left.
Hint Resolve both_mover_right.
Hint Resolve left_mover_left_mover_pred.
Hint Resolve always_enabled_to_stable.
Hint Resolve always_enabled_to_enabled_in.

Arguments left_mover {opT State} op_step {moverT}.
Arguments left_mover_pred {opT State} op_step {moverT}.
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

  Inductive left_movers (P : nat -> State -> Prop) : forall T, proc opT T -> Prop :=
  | LeftMoversOne :
    forall `(opMover : opT oT) `(rx : _ -> proc _ T),
    left_mover_pred op_step opMover P ->
    (forall tid s,
      P tid s ->
      enabled_in op_step opMover tid s) ->
    (forall r,
      left_movers
        (fun tid s' =>
          exists s s0,
            P tid s /\
            exec_any op_step tid s (Op opMover) r s0 /\
            exec_others op_step tid s0 s')
        (rx r)) ->
    left_movers P (Bind (Op opMover) rx)
  | LeftMoversRet :
    forall `(v : T),
    left_movers P (Ret v).

  Inductive at_most_one_non_mover (P : nat -> State -> Prop) : forall T, proc opT T -> Prop :=
  | ZeroNonMovers :
    forall `(p : proc _ T),
    left_movers P p ->
    at_most_one_non_mover P p
  | OneNonMover :
    forall `(op : opT T) `(rx : _ -> proc _ R),
    (forall r,
      left_movers
        (fun tid s' =>
          exists s s0,
            P tid s /\
            exec_any op_step tid s (Op op) r s0 /\
            exec_others op_step tid s0 s')
        (rx r)) ->
    at_most_one_non_mover P (Bind (Op op) rx)
  | OneFinalNonMover :
    forall `(op : opT T),
    at_most_one_non_mover P (Op op)
  .

  Inductive right_movers (P : nat -> State -> Prop) : forall T, proc opT T -> Prop :=
  | RightMoversOne :
    forall `(opMover : opT oT) `(rx : _ -> proc _ T),
    right_mover op_step opMover ->
    (forall r,
      right_movers
        (fun tid s' =>
          exists s s0,
            P tid s /\
            exec_any op_step tid s (Op opMover) r s0 /\
            exec_others op_step tid s0 s')
        (rx r)) ->
    right_movers P (Bind (Op opMover) rx)
  | RightMoversDone :
    forall `(p : proc _ T),
    at_most_one_non_mover P p ->
    right_movers P p.

  Definition ysa_movers `(p : proc opT T) :=
    right_movers
      any
      p.


  Hint Resolve left_mover_pred_impl.

  Theorem left_movers_impl :
    forall (P1 : nat -> State -> Prop) `(p : proc _ T),
      left_movers P1 p ->
      forall (P2 : nat -> State -> Prop),
        (forall tid s, P2 tid s -> P1 tid s) ->
        left_movers P2 p.
  Proof.
    induction 1; intros.
    - econstructor; eauto; intros.
      eapply H2; intros; repeat deex.
      eauto 20.
    - econstructor.
  Qed.

  Theorem at_most_one_non_mover_impl :
    forall (P1 : nat -> State -> Prop) `(p : proc _ T),
      at_most_one_non_mover P1 p ->
      forall (P2 : nat -> State -> Prop),
        (forall tid s, P2 tid s -> P1 tid s) ->
        at_most_one_non_mover P2 p.
  Proof.
    destruct 1; intros.
    - econstructor.
      eapply left_movers_impl; eauto.
    - eapply OneNonMover; intros.
      eapply left_movers_impl; eauto.
      intros; repeat deex.
      eauto 10.
    - eapply OneFinalNonMover.
  Qed.

  Theorem right_movers_impl :
    forall (P1 : nat -> State -> Prop) `(p : proc _ T),
      right_movers P1 p ->
      forall (P2 : nat -> State -> Prop),
        (forall tid s, P2 tid s -> P1 tid s) ->
        right_movers P2 p.
  Proof.
    induction 1; intros.
    - econstructor; eauto; intros.
      eapply H1; intros.
      repeat deex; eauto 10.
    - econstructor.
      eapply at_most_one_non_mover_impl; eauto.
  Qed.


  Theorem trace_incl_atomize_ysa_left_movers :
    forall T L R (p : proc _ T) (l : _ -> proc _ L) (rx : _ -> proc _ R) P s tid,
      (forall r, pred_stable op_step (P r)) ->
      (forall r s',
        exec_any op_step tid s (Atomic p) r s' ->
          (P r) tid s' /\
          left_movers (P r) (l r)) ->
      trace_incl_s s tid op_step
        (Bind (Bind (Atomic p) l) rx)
        (Bind (Atomic (Bind p l)) rx).
  Proof.
    intros.
    eapply trace_incl_s_proof_helper; intros.
    repeat exec_tid_inv.

    cut (exists tr' v1 s1 evs1,
      atomic_exec op_step (l v) tid s' v1 s1 evs1 /\
      exec_prefix op_step s1 ts [[ tid := Proc (rx v1) ]] tr' /\
      tr = (prepend tid evs1 tr')); intros.
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

    edestruct H0; clear H0; eauto.
    specialize (H v).
    remember (P v) as P0; clear HeqP0 P.
    remember (l v).
    clear dependent s.
    clear dependent p.
    clear s0 evs.
    generalize dependent l.
    generalize dependent T.
    generalize dependent s'.
    generalize dependent tr.
    induction H4; intros.

    - repeat rewrite exec_equiv_bind_bind in H4.
      eapply exec_left_mover in H4; eauto; repeat deex.

      edestruct H3.
      eauto.
      eassumption.
      eauto 20.
      reflexivity.

      repeat deex.
      descend; intuition idtac.

      abstract_term evs1; eauto.
      eauto.

    - rewrite exec_equiv_ret_bind in H3.
      descend; intuition idtac.
      eauto.
      eauto.
      eauto.
  Grab Existential Variables.
    all: exact tt.
  Qed.


  Lemma exec_any_atomic_op :
    forall `(op : opT T) s r s' tid,
      exec_any op_step tid s (Atomic (Op op)) r s' ->
      exec_any op_step tid s (Op op) r s'.
  Proof.
    intros.
    remember (Atomic (Op op)).
    induction H; intros; subst; eauto; exec_tid_inv.
    atomic_exec_inv.
    eauto.
  Grab Existential Variables.
    all: exact tt.
  Qed.

  Lemma pred_stable_exec_any_atomic_ret :
    forall P tid s s' `(v : T) r,
      pred_stable op_step P ->
      P tid s ->
      exec_any op_step tid s (Atomic (Ret v)) r s' ->
      P tid s'.
  Proof.
    intros.
    remember (Atomic (Ret v)).
    induction H1; intros; subst; eauto; exec_tid_inv.
    atomic_exec_inv.
    eauto.
  Qed.

  Hint Resolve exec_any_atomic_op.


  Theorem trace_incl_atomize_ysa :
    forall T R (p : proc _ T) (rx : _ -> proc _ R),
      ysa_movers p ->
      trace_incl op_step
        (Bind p rx)
        (Bind (Atomic p) rx).
  Proof.
    unfold ysa_movers.
    intros.
    eapply trace_incl_trace_incl_s; intros.
    assert (any tid s) by firstorder.
    assert (pred_stable op_step any) by eauto.
    generalize dependent (@any State); intros.
    generalize dependent s.
    induction H; intros.
    {
      rewrite <- trace_incl_atomize_op_right_mover by eauto.
      repeat rewrite exec_equiv_bind_bind.
      eapply trace_incl_s_bind_a; eauto 10.
    }

    inversion H; clear H; repeat sigT_eq.
    - rewrite <- exec_equiv_ret_bind with (v := tt) (p0 := (fun _ => p)) at 1.
      rewrite <- atomic_equiv_ret_bind with (v := tt) (p0 := (fun _ => p)).
      erewrite <- trace_incl_atomize_ysa_left_movers with (P := fun _ => P); eauto.
      rewrite exec_equiv_atomicret_ret.
      reflexivity.

      intros; intuition eauto.
      eapply pred_stable_exec_any_atomic_ret; eauto.

    - erewrite <- trace_incl_atomize_ysa_left_movers with (P := fun _ => _).
      repeat rewrite exec_equiv_bind_bind.
      rewrite trace_incl_op.
      reflexivity.

      2: intros; intuition eauto.
      2: simpl.
      2: eauto 20.

      eauto.

    - rewrite trace_incl_op.
      reflexivity.

  Grab Existential Variables.
    all: exact tt.
  Qed.

  Lemma ysa_movers_right_movers :
    forall `(p : proc opT T),
      right_movers any p ->
      ysa_movers p.
  Proof.
    firstorder.
  Qed.

End YSA.

Hint Constructors right_movers.
Hint Constructors at_most_one_non_mover.
Hint Constructors left_movers.
Hint Resolve ysa_movers_right_movers.
