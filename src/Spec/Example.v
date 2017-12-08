Require Import Helpers.Helpers.
Require Import Helpers.ListStuff.
Require Import ConcurProc.
Require Import Equiv.
Require Import Omega.
Require Import FunctionalExtensionality.

Global Set Implicit Arguments.
Global Generalizable All Variables.


(** Opcodes *)

Inductive opT : Type -> Type :=
| Inc : opT nat
| Noop : opT unit.

Inductive opHiT : Type -> Type :=
| IncTwice : opHiT nat
| Noop2 : opHiT unit.

Inductive opHi2T : Type -> Type :=
.


(** State *)

Definition State := forall (tid : nat), nat.

Definition init_state : State := fun tid' => 4.

Definition state_upd (s : State) (tid : nat) (val : nat) :=
  fun tid' =>
    if tid' == tid then val else s tid'.

Definition inc s tid :=
  state_upd s tid (s tid + 1).

Definition inc2 s tid :=
  state_upd s tid (s tid + 2).


(** Semantics *)

Inductive op_step : forall T, opT T -> nat -> State -> T -> State -> Prop :=
| StepInc : forall tid s,
  op_step Inc tid s (s tid + 1) (inc s tid)
| StepNoop : forall tid s,
  op_step Noop tid s tt s.

Inductive opHi_step : forall T, opHiT T -> nat -> State -> T -> State -> Prop :=
| StepIncTwice : forall tid s,
  opHi_step IncTwice tid s (s tid + 2) (inc2 s tid)
| StepNoop2 : forall tid s,
  opHi_step Noop2 tid s tt s.


(** Implementations *)

Definition inc_twice_impl :=
  _ <- OpCallHi IncTwice;
  _ <- Op Inc;
  i2 <- Op Inc;
  OpRetHi i2.

Definition p1 :=
  _ <- inc_twice_impl;
  Ret tt.

Definition ts := threads_empty [[ 1 := Proc p1 ]].


Definition p2 : proc opHiT opHi2T _ :=
  _ <- Op IncTwice;
  Ret tt.

Definition ts2 := threads_empty [[ 1 := Proc p2 ]].



(** Example traces *)

Ltac exec_one tid' :=
  eapply ExecOne with (tid := tid');
    [ rewrite thread_upd_eq; reflexivity | | autorewrite with t ].

Hint Constructors op_step.
Hint Constructors opHi_step.

Definition ex_trace :
  { t : trace opT opHiT | exec op_step init_state ts t }.
Proof.
  eexists.
  unfold ts.
  unfold init_state.
  exec_one 1; eauto; simpl; autorewrite with t.
  exec_one 1; eauto; simpl; autorewrite with t.
  exec_one 1; eauto; simpl; autorewrite with t.
  exec_one 1; eauto; simpl; autorewrite with t.
  exec_one 1; eauto; simpl; autorewrite with t.
  exec_one 1; eauto; simpl; autorewrite with t.
  exec_one 1; eauto; simpl; autorewrite with t.
  exec_one 1; eauto; simpl; autorewrite with t.
  exec_one 1; eauto; simpl; autorewrite with t.
  eapply ExecEmpty; eauto.
Defined.

Eval compute in (proj1_sig ex_trace).


Definition ex_trace2 :
  { t : trace opHiT opHi2T | exec opHi_step init_state ts2 t }.
Proof.
  eexists.
  unfold ts2.
  unfold init_state.
  exec_one 1; eauto; simpl; autorewrite with t.
  exec_one 1; eauto; simpl; autorewrite with t.
  exec_one 1; eauto; simpl; autorewrite with t.
  exec_one 1; eauto; simpl; autorewrite with t.
  eapply ExecEmpty; eauto.
Defined.

Eval compute in (proj1_sig ex_trace2).


Theorem ex_trace_ex_trace2 :
  traces_match (proj1_sig ex_trace) (proj1_sig ex_trace2).
Proof.
  simpl.
  eauto 20.
Qed.


(** Compilation *)

Inductive compile_ok : forall `(p1 : proc opT opHiT T) `(p2 : proc opHiT opHi2T T), Prop :=
| CompileIncTwice :
  compile_ok (inc_twice_impl) (Op IncTwice)
| CompileRet : forall `(x : T),
  compile_ok (Ret x) (Ret x)
| CompileBind : forall `(p1a : proc opT opHiT T1) (p2a : proc opHiT opHi2T T1)
                       `(p1b : T1 -> proc opT opHiT T2) (p2b : T1 -> proc opHiT opHi2T T2),
  compile_ok p1a p2a ->
  (forall x, compile_ok (p1b x) (p2b x)) ->
  compile_ok (Bind p1a p1b) (Bind p2a p2b).

Hint Constructors compile_ok.

Theorem ex_compile_ok : compile_ok p1 p2.
Proof.
  unfold p1, p2.
  eauto.
Qed.

Hint Resolve ex_compile_ok.


Definition threads_compile_ok (ts1 : @threads_state opT opHiT) (ts2 : @threads_state opHiT opHi2T) :=
  forall tid,
    ts1 [[ tid ]] = NoProc /\ ts2 [[ tid ]] = NoProc \/
  (exists T (p1 : proc _ _ T) p2,
    ts1 [[ tid ]] = Proc p1 /\ ts2 [[ tid ]] = Proc p2 /\ compile_ok p1 p2).

Theorem ex_ts_compile_ok : threads_compile_ok ts ts2.
Proof.
  unfold threads_compile_ok, ts, ts2, thread_upd, threads_empty; intros.
  destruct tid; subst; compute; eauto.
  destruct tid; subst; compute; eauto 10.
  destruct tid; subst; compute; eauto.
Qed.


Ltac thread_inv :=
  match goal with
  | H : thread_get (thread_upd _ _ _) _ = Proc _ |- _ =>
    eapply thread_upd_inv in H; destruct H; (intuition idtac); subst
  | H : thread_get threads_empty _ = Proc _ |- _ =>
    eapply thread_empty_inv in H; exfalso; apply H
  | H : (_, _) = (_, _) |- _ =>
    inversion H; clear H; subst; repeat sigT_eq
  | H : _ = Bind _ _ |- _ =>
    solve [ inversion H ]
  | H : _ = Ret _ |- _ =>
    solve [ inversion H ]
  | H : no_runnable_threads (thread_upd _ _ _) |- _ =>
    solve [ eapply thread_upd_not_empty in H; exfalso; eauto ]
  | H : _ _ = Proc _ |- _ =>
    solve [ exfalso; eapply no_runnable_threads_some; eauto ]
  | H : _ = _ |- _ =>
    congruence
  | H : _ = _ \/ _ = _ |- _ =>
    solve [ intuition congruence ]
  | H : ?a = ?a |- _ =>
    clear H
  end || maybe_proc_inv.

Ltac bind_inv :=
  match goal with
  | H : _ = Bind _ _ |- _ =>
    inversion H; clear H; subst; repeat sigT_eq
  end.

Ltac exec_inv :=
  match goal with
  | H : exec _ _ _ _ |- _ =>
    inversion H; clear H; subst
  end;
  autorewrite with t in *.

Ltac empty_inv :=
  try solve [ exfalso; eapply thread_empty_inv; eauto ].

Ltac step_inv :=
  match goal with
  | H : op_step _ _ _ _ _ |- _ =>
    inversion H; clear H; subst; repeat sigT_eq
  | H : opHi_step _ _ _ _ _ |- _ =>
    inversion H; clear H; subst; repeat sigT_eq
  end.


Theorem ex_all_traces_match :
  forall s tr1 tr2,
  exec op_step s ts tr1 ->
  exec opHi_step s ts2 tr2 ->
  traces_match tr1 tr2.
Proof.
  intros.
  unfold ts, ts2 in *.

  repeat ( exec_inv; repeat thread_inv;
    try ( repeat exec_tid_inv; repeat thread_inv ) ).
  repeat step_inv.

  unfold inc, state_upd; simpl.
  replace (s' 1 + 1 + 1) with (s' 1 + 2) by omega.
  eauto 20.
Qed.


(** Commutativity *)

Ltac destruct_ifs :=
  repeat match goal with
  | |- context[if ?a == ?b then _ else _] =>
    destruct (a == b)
  end.

Lemma inc_commutes_op_step : forall T (op : opT T) tid s v s',
  op_step op tid s v s' ->
  forall tid0,
  tid0 <> tid ->
  op_step op tid
    (inc s tid0)
    v
    (inc s' tid0).
Proof.
  intros; step_inv.
  + replace (s tid + 1) with ((inc s tid0) tid + 1).
    replace (inc (inc s tid) tid0) with (inc (inc s tid0) tid).
    constructor.
    unfold inc, state_upd; apply functional_extensionality; intros.
      destruct_ifs; omega.
    unfold inc, state_upd.
      destruct_ifs; omega.
  + constructor.
Qed.

Lemma inc_commutes_op_step' : forall T (op : opT T) tid s v s',
  op_step op tid s v s' ->
  forall tid0,
  tid0 <> tid ->
  s tid0 = s' tid0.
Proof.
  intros; step_inv.
  + unfold inc, state_upd.
      destruct_ifs; omega.
  + congruence.
Qed.

Lemma inc_commutes_exec_tid : forall tid0 tid1 T s p s' result' evs,
  tid0 <> tid1 ->
  @exec_tid opT opHiT State op_step T tid1 s p s' result' evs ->
  @exec_tid opT opHiT State op_step T tid1 (inc s tid0) p (inc s' tid0) result' evs.
Proof.
  intros.
  induction H0; simpl; eauto.
  - constructor.
    eapply inc_commutes_op_step; eauto.
  - constructor.
    induction H0; eauto.
    constructor.
    eapply inc_commutes_op_step; eauto.
Qed.

Lemma inc_commutes_exec_tid' : forall T tid0 s p s' result' evs,
  @exec_tid opT opHiT State op_step T tid0 s p s' result' evs ->
  forall tid1, tid0 <> tid1 ->
  s tid1 = s' tid1.
Proof.
  intros.
  induction H; eauto.
  - eapply inc_commutes_op_step'; eauto.
  - induction H; eauto.
    + eapply eq_trans.
      apply IHatomic_exec1; eauto.
      apply IHatomic_exec2; eauto.
    + eapply inc_commutes_op_step'; eauto.
Qed.

Theorem inc_commutes_0 :
  forall T (p1 p2 : _ -> proc opT opHiT T),
  (forall r, hitrace_incl op_step (p1 r) (p2 r)) ->
  forall s tid,
  hitrace_incl_s s (inc s tid) tid
    op_step
    (r <- OpExec Inc; p1 r) (p2 (s tid + 1)).
Proof.
  unfold hitrace_incl_s, hitrace_incl_ts_s; intros.

  match goal with
  | H : exec _ _ (thread_upd ?ts ?tid ?p) _ |- _ =>
    remember (thread_upd ts tid p);
    generalize dependent ts;
    induction H0; intros; subst
  end.

  - destruct (tid0 == tid); subst.
    + autorewrite with t in *.
      repeat maybe_proc_inv.
      repeat exec_tid_inv.
      step_inv.
      edestruct H; eauto.

    + edestruct IHexec.
      rewrite thread_upd_upd_ne; eauto.
      intuition idtac.

      eexists; split.
      eapply ExecOne with (tid := tid0).
        autorewrite with t in *; eauto.
        eapply inc_commutes_exec_tid; eauto.
        rewrite thread_upd_upd_ne; eauto.
        erewrite inc_commutes_exec_tid' with (s := s) (tid1 := tid);
          eauto.
      eauto.

  - exfalso; eauto.
Qed.

Theorem inc_commutes_1 :
  forall `(ap : proc opT opHiT TA)
         `(p1 : proc opT opHiT T')
         (p2 : _ -> proc opT opHiT T'),
  (forall s tid,
    hitrace_incl_s s (inc s tid) tid op_step
      p1 (p2 (s tid + 1))) ->
  hitrace_incl op_step
    (_ <- Atomic ap; p1)
    (r <- Atomic (_ <- ap; Op Inc); p2 r).
Proof.
  unfold hitrace_incl, hitrace_incl_opt,
         hitrace_incl_ts, hitrace_incl_ts_s; intros.

  match goal with
  | H : exec _ _ (thread_upd ?ts ?tid ?p) _ |- _ =>
    remember (thread_upd ts tid p);
    generalize dependent ts;
    induction H0; intros; subst
  end.

  - destruct (tid0 == tid); subst.
    + autorewrite with t in *.
      repeat maybe_proc_inv.
      repeat exec_tid_inv.

      eapply H in H2. deex.

      eexists; split.

      eapply ExecOne with (tid := tid).
        autorewrite with t; eauto.
        eauto 20.
        autorewrite with t; eauto.

      rewrite prepend_app. simpl. eauto.

    + edestruct IHexec.
      rewrite thread_upd_upd_ne; eauto.
      intuition idtac.

      eexists; split.
      eapply ExecOne with (tid := tid0).
        autorewrite with t in *; eauto.
        eauto.
        rewrite thread_upd_upd_ne; auto.
      eauto.
      eauto.

  - exfalso; eauto.
Qed.

Theorem inc_commutes_final :
  forall `(ap : proc _ _ TA) `(p : _ -> proc opT opHiT T'),
  hitrace_incl op_step
    (_ <- Atomic ap; r <- Op Inc; p r)
    (r <- Atomic (_ <- ap; Op Inc); p r).
Proof.
  intros.
  eapply inc_commutes_1.

  intros; unfold Op.
  rewrite exec_equiv_bind_bind.
  setoid_rewrite exec_equiv_bind_bind.
  rewrite hitrace_incl_opcall.
  eapply inc_commutes_0.

  intros.
  rewrite hitrace_incl_opret.
  reflexivity.
Qed.


(** Atomicity *)

Definition p1_a :=
  _ <- Atomic inc_twice_impl;
  Ret tt.

Definition ts_a := threads_empty [[ 1 := Proc p1_a ]].


Theorem ts_equiv_ts_a : forall s,
  hitrace_incl_ts op_step s ts ts_a.
Proof.
  unfold hitrace_incl_ts, hitrace_incl_ts_s.
  intros.
  unfold ts, ts_a in *.

  repeat ( exec_inv; repeat thread_inv;
    try ( repeat exec_tid_inv; repeat thread_inv ) ).

  repeat step_inv.
  unfold p1_a.

  eexists; split.

  exec_one 1; eauto 20; simpl; autorewrite with t.
  exec_one 1; eauto 20; simpl; autorewrite with t.
  eapply ExecEmpty; eauto.

  reflexivity.
Qed.


Definition inc_twice_impl_atomic :=
  _ <- OpCallHi IncTwice;
  r <- Atomic (_ <- Op Inc; Op Inc);
  OpRetHi r.

Theorem inc_twice_atomic : forall `(rx : _ -> proc _ _ T),
  hitrace_incl op_step
    (Bind inc_twice_impl rx) (Bind inc_twice_impl_atomic rx).
Proof.
  unfold inc_twice_impl, inc_twice_impl_atomic; intros.

  rewrite exec_equiv_bind_bind.
  rewrite exec_equiv_bind_bind with (p1 := OpCallHi _).
  eapply hitrace_incl_bind_a; intros.

  rewrite exec_equiv_bind_bind.
  rewrite exec_equiv_bind_bind with (p1 := Atomic _).
  rewrite hitrace_incl_op.

  setoid_rewrite exec_equiv_bind_bind with (p1 := Op _).
  rewrite inc_commutes_final.
  reflexivity.
Qed.
