Require Import Helpers.Helpers.
Require Import Helpers.ListStuff.
Require Import ConcurProc.
Require Import Equiv.
Require Import Omega.
Require Import FunctionalExtensionality.
Require Import Relations.Relation_Operators.
Require Import RelationClasses.
Require Import Morphisms.

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

Inductive compile_ok : forall T `(p1 : proc opT opHiT T) `(p2 : proc opHiT opHi2T T), Prop :=
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


(** Correctness for 1 thread *)

Definition trace_match_one_thread {opLoT opMidT opHiT State T} lo_step hi_step
                                            (p1 : proc opLoT opMidT T)
                                            (p2 : proc opMidT opHiT T) :=
  forall (s : State) tr1,
    exec lo_step s (threads_empty [[ 1 := Proc p1 ]]) tr1 ->
    exists tr2,
      exec hi_step s (threads_empty [[ 1 := Proc p2 ]]) tr2 /\
      traces_match tr1 tr2.

Instance trace_match_one_thread_proper {opLoT opMidT opHiT State T lo_step hi_step} :
  Proper (exec_equiv ==> exec_equiv ==> Basics.flip Basics.impl)
         (@trace_match_one_thread opLoT opMidT opHiT State T lo_step hi_step).
Proof.
  intros p1 p1'; intros.
  intros p2 p2'; intros.
  unfold Basics.flip, Basics.impl; intros.
  unfold trace_match_one_thread in *; intros.
  apply H in H2.
  apply H1 in H2.
  destruct H2.
  eexists; intuition eauto.
  apply H0. eauto.
Qed.

Instance trace_match_one_thread_proper2 {opLoT opMidT opHiT State T lo_step hi_step} :
  Proper (hitrace_incl lo_step ==> exec_equiv ==> Basics.flip Basics.impl)
         (@trace_match_one_thread opLoT opMidT opHiT State T lo_step hi_step).
Proof.
  intros p1 p1'; intros.
  intros p2 p2'; intros.
  unfold Basics.flip, Basics.impl; intros.
  unfold trace_match_one_thread in *; intros.
  eapply H in H2. deex.
  apply H1 in H2. deex.
  eexists; intuition eauto.
  apply H0. eauto.
  rewrite H3. eauto.
Qed.

Theorem all_single_thread_traces_match' :
  forall T T' (p1 : proc opT opHiT T) (p2 : proc opHiT opHi2T T) (p1rest : T -> proc opT opHiT T') (p2rest : T -> proc opHiT opHi2T T'),
  (forall x, trace_match_one_thread op_step opHi_step (p1rest x) (p2rest x)) ->
  compile_ok p1 p2 ->
  trace_match_one_thread op_step opHi_step (Bind p1 p1rest) (Bind p2 p2rest).
Proof.
  intros.
  generalize dependent p2rest.
  generalize dependent p1rest.
  induction H0; intros.

  - rewrite inc_twice_atomic.

    unfold trace_match_one_thread; intros.

    exec_inv; repeat thread_inv.
    autorewrite with t in *.
    repeat ( exec_tid_inv; intuition try congruence ).

    exec_inv; repeat thread_inv.
    autorewrite with t in *.
    repeat ( exec_tid_inv; intuition try congruence ).

    repeat match goal with
    | H : atomic_exec _ _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    end.
    repeat step_inv.

    exec_inv; repeat thread_inv.
    autorewrite with t in *.
    repeat ( exec_tid_inv; intuition try congruence ).

    apply H in H3. deex.

    eexists; split.
    eapply ExecOne with (tid := 1).
      rewrite thread_upd_eq; auto.
      eauto.
    eapply ExecOne with (tid := 1).
      rewrite thread_upd_eq; auto.
      eauto.
    eapply ExecOne with (tid := 1).
      rewrite thread_upd_eq; auto.
      eauto.
    autorewrite with t.

    match goal with
    | H : exec _ ?s1 (thread_upd _ _ (Proc ?p1)) _ |-
          exec _ ?s2 (thread_upd _ _ (Proc ?p2)) _ =>
      replace p2 with p1; [ replace s2 with s1; [ eauto | ] | ]
    end.

    unfold inc, inc2, state_upd; apply functional_extensionality; intros.
      destruct_ifs; omega.
    f_equal.
    unfold inc, inc2, state_upd;
      destruct_ifs; omega.

    simpl.
    replace (inc s1 1 1 + 1) with (s1 1 + 2).
    eauto 20.
    unfold inc, state_upd. destruct_ifs; omega.

  - unfold trace_match_one_thread in *; intros.

    exec_inv; repeat thread_inv; autorewrite with t in *.
    repeat exec_tid_inv; try intuition congruence.

    edestruct H; eauto. intuition try congruence.
    eexists. split.

    exec_one 1.
      eapply ExecTidBind. eauto. eauto.
      autorewrite with t; simpl.

    eauto.

  - rewrite exec_equiv_bind_bind.
    rewrite exec_equiv_bind_bind.
    eapply IHcompile_ok.
    intros.
    eapply H1.
    eapply H2.
Qed.

Theorem all_single_thread_traces_match :
  forall T' (p1 : proc opT opHiT T') (p2 : proc opHiT opHi2T T'),
  compile_ok p1 p2 ->
  trace_match_one_thread op_step opHi_step p1 p2.
Proof.
  intros.
  unfold trace_match_one_thread; intros.
  eapply exec_equiv_bind_ret in H0.
  eapply all_single_thread_traces_match' in H0; eauto.
  deex.
  eexists; split; eauto.
  eapply exec_equiv_bind_ret.
  eauto.

  clear H0.
  unfold trace_match_one_thread; intros.
  eapply exec_equiv_ret_None in H0.
  exec_inv; repeat thread_inv.

  eexists; split.
  eapply exec_equiv_ret_None.
  eapply ExecEmpty; eauto.

  eauto.
Qed.


(** Many-thread correctness *)

Inductive compile_ok_atomic : forall T (p1 : proc opT opHiT T) (p2 : proc opHiT opHi2T T), Prop :=
| CompileAIncTwiceCall :
  compile_ok_atomic (OpCallHi IncTwice) (OpCall IncTwice)
| CompileAIncTwiceExec :
  compile_ok_atomic (Atomic (_ <- Op Inc; Op Inc)) (OpExec IncTwice)
| CompileAIncTwiceRet : forall `(r : T),
  compile_ok_atomic (OpRetHi r) (OpRet r)
| CompileARet : forall `(x : T),
  compile_ok_atomic (Ret x) (Ret x)
| CompileABind : forall `(p1a : proc opT opHiT T1) (p2a : proc opHiT opHi2T T1)
                        `(p1b : T1 -> proc opT opHiT T2) (p2b : T1 -> proc opHiT opHi2T T2),
  compile_ok_atomic p1a p2a ->
  (forall x, compile_ok_atomic (p1b x) (p2b x)) ->
  compile_ok_atomic (Bind p1a p1b) (Bind p2a p2b).

Definition compile_ok_all_atomic (ts1 ts2 : threads_state) :=
  proc_match compile_ok_atomic ts1 ts2.

Lemma compile_ok_atomic_exec_tid : forall T (p1 : proc _ _ T) p2,
  compile_ok_atomic p1 p2 ->
  forall tid s s' result evs,
  exec_tid op_step tid s p1 s' result evs ->
  exists result' evs',
  exec_tid opHi_step tid s p2 s' result' evs' /\
  traces_match (prepend tid evs TraceEmpty) (prepend tid evs' TraceEmpty) /\
  match result with
  | inl v => match result' with
    | inl v' => v = v'
    | inr _ => False
    end
  | inr p' => match result' with
    | inl _ => False
    | inr p'' => compile_ok_atomic p' p''
    end
  end.
Proof.
  induction 1; intros.

  - exec_tid_inv.
    do 2 eexists; split.
    constructor.
    split.
    simpl; eauto.
    eauto.

  - exec_tid_inv.
    repeat match goal with
    | H : atomic_exec _ _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    end.
    repeat step_inv.
    do 2 eexists; split.
    constructor.

    replace (inc (inc s1 tid) tid) with (inc2 s1 tid).
    constructor.

    unfold inc, inc2, state_upd; apply functional_extensionality; intros.
      destruct_ifs; omega.

    split.
    simpl; eauto.

    unfold inc, inc2, state_upd;
      destruct_ifs; omega.

  - exec_tid_inv.
    do 2 eexists; split.
    constructor.
    split.
    simpl; eauto.
    eauto.

  - exec_tid_inv.
    do 2 eexists; split.
    constructor.
    split.
    simpl; eauto.
    eauto.

  - exec_tid_inv.
    eapply IHcompile_ok_atomic in H12.
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
Qed.

Theorem all_traces_match_0 :
  forall ts1 ts2,
  compile_ok_all_atomic ts1 ts2 ->
  traces_match_ts op_step opHi_step ts1 ts2.
Proof.
  unfold traces_match_ts; intros.
  generalize dependent ts3.
  induction H0; intros.
  - eapply proc_match_pick with (tid := tid) in H2 as H'.
    intuition try congruence.
    repeat deex.
    rewrite H3 in H; inversion H; clear H; subst.
    repeat maybe_proc_inv.

    edestruct compile_ok_atomic_exec_tid; eauto.
    repeat deex.

    edestruct IHexec.
    shelve.
    intuition idtac.

    eexists; split.
    eapply ExecOne with (tid := tid).
      eauto.
      eauto.
      eauto.

    eapply traces_match_prepend; eauto.
    Unshelve.

    destruct result, x; simpl in *; try solve [ exfalso; eauto ].
    eapply proc_match_del; eauto.
    eapply proc_match_upd; eauto.

  - eexists; split.
    eapply ExecEmpty.
    2: eauto.

    unfold compile_ok_all_atomic in *.
    eauto.
Qed.

Inductive atomize_ok : forall T (p1 : proc opT opHiT T) (p2 : proc opT opHiT T), Prop :=
| AtomizeIncTwice :
  atomize_ok (inc_twice_impl) (inc_twice_impl_atomic)
| AtomizeRet : forall T (x : T),
  atomize_ok (Ret x) (Ret x)
| AtomizeBind : forall T1 T2 (p1a p2a : proc opT opHiT T1)
                             (p1b p2b : T1 -> proc opT opHiT T2),
  atomize_ok p1a p2a ->
  (forall x, atomize_ok (p1b x) (p2b x)) ->
  atomize_ok (Bind p1a p1b) (Bind p2a p2b).

Definition atomize_ok_all (ts1 ts2 : threads_state) :=
  proc_match atomize_ok ts1 ts2.

Definition compile_ok_all (ts1 ts2 : threads_state) :=
  proc_match compile_ok ts1 ts2.

Fixpoint compile_atomic T (p : proc opHiT opHi2T T) : proc opT opHiT T :=
  match p with
  | Ret t => Ret t
  | OpCall op => OpCallHi op
  | OpExec op =>
    match op with
    | IncTwice => Atomic (_ <- Op Inc; Op Inc)
    | Noop2 => Atomic (Ret tt)
    end
  | OpRet r => OpRetHi r
  | Bind p1 p2 =>
    Bind (compile_atomic p1) (fun r => compile_atomic (p2 r))
  | OpCallHi _ => Ret tt
  | OpRetHi v => Ret v
  | Atomic p => Atomic (compile_atomic p)
  end.

Definition atomize_ok_all_upto n (ts1 ts2 : threads_state) :=
  proc_match_upto n atomize_ok ts1 ts2.

Print hitrace_incl_opt.

Theorem atomize_ok_preserves_trace_0 :
  forall T p1 p2,
  atomize_ok p1 p2 ->
  forall T' (p1rest p2rest : T -> proc _ _ T'),
  (forall x, hitrace_incl op_step (p1rest x) (p2rest x)) ->
  hitrace_incl op_step (Bind p1 p1rest) (Bind p2 p2rest).
Proof.
  induction 1; intros.
  - rewrite inc_twice_atomic.
    eapply hitrace_incl_bind_a.
    eauto.
  - eapply hitrace_incl_bind_a.
    eauto.
  - rewrite exec_equiv_bind_bind.
    rewrite exec_equiv_bind_bind.
    eapply IHatomize_ok.
    eauto.
Qed.

Theorem atomize_ok_preserves_trace :
  forall `(p1 : proc _ _ T) p2,
  atomize_ok p1 p2 ->
  hitrace_incl op_step p1 p2.
Proof.
  intros.
  rewrite <- exec_equiv_bind_ret.
  rewrite <- exec_equiv_bind_ret with (p := p4).
  eapply atomize_ok_preserves_trace_0; eauto.
  reflexivity.
Qed.

Theorem atomize_ok_all_upto_preserves_trace :
  forall n ts1' ts1,
  atomize_ok_all_upto n ts1 ts1' ->
    forall s,
      hitrace_incl_ts op_step s ts1 ts1'.
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
          admit.
       -- repeat deex.
          rewrite H.
          rewrite atomize_ok_preserves_trace; eauto.
          rewrite thread_upd_same; eauto.
          reflexivity.
    + eapply IHn.
      eapply proc_match_upto_Sn'.
      omega.
      eauto.
Admitted.

Theorem atomize_ok_all_preserves_trace :
  forall ts1' ts1,
  atomize_ok_all ts1 ts1' ->
    forall s,
      hitrace_incl_ts op_step s ts1 ts1'.
Proof.
  intros.
  eapply atomize_ok_all_upto_preserves_trace.
  eapply proc_match_upto_all.
  eauto.
Qed.

Theorem all_traces_match_1 :
  forall ts1 ts1' ts2,
  atomize_ok_all ts1 ts1' ->
  compile_ok_all_atomic ts1' ts2 ->
  traces_match_ts op_step opHi_step ts1 ts2.
Proof.
  unfold trace_match_threads; intros.
  eapply atomize_ok_all_preserves_trace in H; eauto.
  deex.
  edestruct all_traces_match_0; eauto.
  intuition idtac.
  eexists; split.
  eauto.
  eapply traces_match_trace_match_hi; eauto.
  symmetry; eauto.
Qed.

Theorem make_one_atomic :
  forall T p2 (p1 : proc _ _ T),
  compile_ok p1 p2 ->
    atomize_ok p1 (compile_atomic p2) /\
    compile_ok_atomic (compile_atomic p2) p2.
Proof.
  induction 1; simpl; intros.
  - split. constructor. repeat constructor.
  - split; constructor.
  - intuition idtac.
    constructor. eauto. intros. specialize (H1 x). intuition eauto.
    constructor. eauto. intros. specialize (H1 x). intuition eauto.
Qed.

Lemma atomize_ok_cons : forall T (p1 : proc _ _ T) p2 ts1 ts2,
  atomize_ok_all ts1 ts2 ->
  atomize_ok p1 p2 ->
  atomize_ok_all (Some (existT _ _ p1) :: ts1) (Some (existT _ _ p2) :: ts2).
Proof.
  intros.
  intro tid; destruct tid.
  - unfold thread_get; simpl. right. do 3 eexists. eauto.
  - apply H.
Qed.

Lemma atomize_ok_cons_None : forall ts1 ts2,
  atomize_ok_all ts1 ts2 ->
  atomize_ok_all (None :: ts1) (None :: ts2).
Proof.
  intros.
  intro tid; destruct tid.
  - unfold thread_get; simpl. left; eauto.
  - apply H.
Qed.

Lemma compile_ok_atomic_cons : forall T (p1 : proc _ _ T) p2 ts1 ts2,
  compile_ok_all_atomic ts1 ts2 ->
  compile_ok_atomic p1 p2 ->
  compile_ok_all_atomic (Some (existT _ _ p1) :: ts1) (Some (existT _ _ p2) :: ts2).
Proof.
  intros.
  intro tid; destruct tid.
  - unfold thread_get; simpl. right. do 3 eexists. eauto.
  - apply H.
Qed.

Lemma compile_ok_atomic_cons_None : forall ts1 ts2,
  compile_ok_all_atomic ts1 ts2 ->
  compile_ok_all_atomic (None :: ts1) (None :: ts2).
Proof.
  intros.
  intro tid; destruct tid.
  - unfold thread_get; simpl. left; eauto.
  - apply H.
Qed.

Hint Resolve atomize_ok_cons.
Hint Resolve atomize_ok_cons_None.
Hint Resolve compile_ok_atomic_cons.
Hint Resolve compile_ok_atomic_cons_None.

Theorem make_all_atomic :
  forall ts1 ts2,
  compile_ok_all ts1 ts2 ->
  exists ts1',
    atomize_ok_all ts1 ts1' /\
    compile_ok_all_atomic ts1' ts2.
Proof.
  induction ts1; intros.
  - exists nil; split.
    intro tid; left; unfold thread_get; repeat rewrite nth_error_nil; eauto.
    intro tid.
    specialize (H tid); intuition; repeat deex.
    exfalso.
    unfold thread_get in H.
    rewrite nth_error_nil in H. congruence.
  - destruct ts3.
    + exists nil; split.
      2: intro tid; left; unfold thread_get; repeat rewrite nth_error_nil; eauto.
      intro tid.
      specialize (H tid); intuition; repeat deex.
      2: unfold thread_get in H0; rewrite nth_error_nil in H0; congruence.
      left. intuition eauto.
      unfold thread_get; rewrite nth_error_nil; eauto.
    + edestruct IHts1.
      * intro tid. specialize (H (S tid)).
        apply H.
      * intuition.
        destruct o; destruct a.
       -- destruct s.
          destruct s0.
          specialize (H 0) as H'.
            unfold thread_get in H'; simpl in H'. intuition try congruence.
          repeat deex.
          inversion H0; clear H0.
          inversion H3; clear H3.
          subst; repeat sigT_eq'.

          edestruct (make_one_atomic H4).
          exists (Some (existT _ _ (compile_atomic p4)) :: x).
          split; eauto.
       -- specialize (H 0); unfold thread_get in H; simpl in H;
            intuition try congruence.
          repeat deex; intuition congruence.
       -- specialize (H 0); unfold thread_get in H; simpl in H;
            intuition try congruence.
          repeat deex; intuition congruence.
       -- exists (None :: x). eauto.
Qed.

Theorem all_traces_match :
  forall ts1 ts2,
  compile_ok_all ts1 ts2 ->
  trace_match_threads op_step opHi_step ts1 ts2.
Proof.
  intros.
  eapply make_all_atomic in H; deex.
  eapply all_traces_match_1; eauto.
Qed.
