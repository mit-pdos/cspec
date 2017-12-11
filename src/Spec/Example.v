Require Import Helpers.Helpers.
Require Import Helpers.ListStuff.
Require Import ConcurProc.
Require Import Equiv.
Require Import Omega.
Require Import FunctionalExtensionality.
Require Import Relations.Relation_Operators.
Require Import RelationClasses.
Require Import Morphisms.
Require Import List.
Require Import Compile.

Import ListNotations.

Global Set Implicit Arguments.
Global Generalizable All Variables.


(** Opcodes *)

Inductive opT : Type -> Type :=
| Inc : opT nat
| Dec : opT nat
| Noop : opT unit.

Inductive opHiT : Type -> Type :=
| IncTwice : opHiT nat
| DecThrice : opHiT nat
| Noop2 : opHiT unit.

Inductive opHi2T : Type -> Type :=
.


(** State *)

Definition State := forall (tid : nat), nat.

Definition init_state : State := fun tid' => 4.

Definition inc s tid :=
  state_upd s tid (s tid + 1).

Definition inc2 s tid :=
  state_upd s tid (s tid + 2).

Definition dec s tid :=
  state_upd s tid (s tid - 1).

Definition dec3 s tid :=
  state_upd s tid (s tid - 3).


(** Semantics *)

Inductive op_step : forall T, opT T -> nat -> State -> T -> State -> Prop :=
| StepInc : forall tid s,
  op_step Inc tid s (s tid + 1) (inc s tid)
| StepDec : forall tid s,
  op_step Dec tid s (s tid - 1) (dec s tid)
| StepNoop : forall tid s,
  op_step Noop tid s tt s.

Inductive opHi_step : forall T, opHiT T -> nat -> State -> T -> State -> Prop :=
| StepIncTwice : forall tid s,
  opHi_step IncTwice tid s (s tid + 2) (inc2 s tid)
| StepDecThrice : forall tid s,
  opHi_step DecThrice tid s (s tid - 3) (dec3 s tid)
| StepNoop2 : forall tid s,
  opHi_step Noop2 tid s tt s.

Hint Extern 1 (op_step _ _ _ _ _) => econstructor.
Hint Extern 1 (opHi_step _ _ _ _ _) => econstructor.


(** Implementations *)

Definition inc_twice_core : proc opT opHiT _ :=
  _ <- Op Inc;
  Op Inc.

Definition dec_thrice_core : proc opT opHiT _ :=
  _ <- Op Dec;
  _ <- Op Dec;
  Op Dec.

Definition compile_op T (op : opHiT T) : proc opT opHiT T :=
  match op with
  | IncTwice => inc_twice_core
  | DecThrice => dec_thrice_core
  | Noop2 => Ret tt
  end.

Definition inc_twice_impl :=
  hicall compile_op IncTwice.

Definition dec_thrice_impl :=
  hicall compile_op DecThrice.

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
  exec_one 1; eauto 20; simpl; autorewrite with t.
  exec_one 1; eauto 20; simpl; autorewrite with t.
  exec_one 1; eauto 20; simpl; autorewrite with t.
  exec_one 1; eauto 20; simpl; autorewrite with t.
  exec_one 1; eauto 20; simpl; autorewrite with t.
  exec_one 1; eauto 20; simpl; autorewrite with t.
  exec_one 1; eauto 20; simpl; autorewrite with t.
  exec_one 1; eauto 20; simpl; autorewrite with t.
  exec_one 1; eauto 20; simpl; autorewrite with t.
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

Definition inc2_compile_ok :=
  @compile_ok opT opHiT opHi2T compile_op.

Theorem ex_compile_ok : inc2_compile_ok p1 p2.
Proof.
  unfold p1, p2.
  unfold inc2_compile_ok.
  unfold inc_twice_impl.
  econstructor.
  econstructor.
  econstructor.
Qed.

Hint Resolve ex_compile_ok.


Definition threads_compile_ok (ts1 : @threads_state opT opHiT) (ts2 : @threads_state opHiT opHi2T) :=
  proc_match inc2_compile_ok ts1 ts2.


Opaque hicall Op.

Theorem ex_ts_compile_ok : threads_compile_ok ts ts2.
Proof.
  unfold threads_compile_ok, ts, ts2, thread_upd, threads_empty; intros.
  unfold proc_match. split. cbn. eauto.
  intros.
  destruct tid; subst; compute; eauto 20.
  destruct tid; subst; compute; eauto 20.
  destruct tid; subst; compute; eauto 20.
Qed.

Transparent hicall Op.


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

Lemma op_step_commutes :
  step_commutes op_step.
Proof.
  unfold step_commutes; intros; repeat step_inv;
    unfold inc, dec.
  all: eexists; split; eauto.
  all: rewrite state_upd_ne; eauto.
  all: rewrite state_upd_upd_ne; eauto.
  all: match goal with
    | |- op_step _ ?tid ?ss ?r _ =>
      replace (s tid) with (ss tid); eauto;
        unfold inc, dec; rewrite state_upd_ne; eauto
    end.
Qed.

Hint Resolve op_step_commutes.


(** Atomicity *)

Definition p1_a :=
  _ <- Atomic inc_twice_impl;
  Ret tt.

Definition ts_a := threads_empty [[ 1 := Proc p1_a ]].


Theorem ts_equiv_ts_a :
  hitrace_incl_ts op_step ts ts_a.
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



Definition inc_twice_impl_atomic := hicall (atomize compile_op) IncTwice.
Definition dec_thrice_impl_atomic := hicall (atomize compile_op) DecThrice.


Theorem inc_twice_atomic : forall `(rx : _ -> proc _ _ T),
  hitrace_incl op_step
    (Bind inc_twice_impl rx) (Bind inc_twice_impl_atomic rx).
Proof.
  unfold inc_twice_impl, inc_twice_impl_atomic, hicall, atomize; simpl.
  unfold inc_twice_core; intros.

  rewrite exec_equiv_bind_bind.
  rewrite exec_equiv_bind_bind with (p1 := OpCallHi _).
  eapply hitrace_incl_bind_a; intros.
  repeat rewrite exec_equiv_bind_bind.

  (* First [Op Inc] *)
  unfold Op at 3.
  rewrite atomic_equiv_bind_bind with (p1 := OpCall _).
  setoid_rewrite atomic_equiv_bind_bind with (p1 := OpExec _).

  unfold Op at 1.
  rewrite <- hitrace_incl_atomize_opcall.
  rewrite exec_equiv_bind_bind.
  setoid_rewrite exec_equiv_bind_bind.
  eapply hitrace_incl_bind_a; intros.

  rewrite <- hitrace_incl_atomize_opexec; eauto.
  rewrite exec_equiv_bind_bind.
  eapply hitrace_incl_bind_a; intros.

  rewrite <- hitrace_incl_atomize_opret.
  rewrite exec_equiv_bind_bind.
  eapply hitrace_incl_bind_a; intros.

  (* Second [Op Inc] *)
  unfold Op at 2.

  unfold Op at 1.
  rewrite <- hitrace_incl_atomize_opcall.
  rewrite exec_equiv_bind_bind.
  setoid_rewrite exec_equiv_bind_bind.
  eapply hitrace_incl_bind_a; intros.

  rewrite <- hitrace_incl_atomize_opexec; eauto.
  rewrite exec_equiv_bind_bind.
  eapply hitrace_incl_bind_a; intros.

  rewrite <- atomic_equiv_bind_ret with (p := OpRet x4) at 2.
  rewrite <- hitrace_incl_atomize_opret.
  rewrite exec_equiv_bind_bind.
  eapply hitrace_incl_bind_a; intros.

  rewrite exec_equiv_atomicret_bind.
  reflexivity.
Qed.

Theorem dec_thrice_atomic : forall `(rx : _ -> proc _ _ T),
  hitrace_incl op_step
    (Bind dec_thrice_impl rx) (Bind dec_thrice_impl_atomic rx).
Proof.
  unfold dec_thrice_impl, dec_thrice_impl_atomic, hicall, atomize; simpl.
  unfold dec_thrice_core; intros.

  rewrite exec_equiv_bind_bind.
  rewrite exec_equiv_bind_bind with (p1 := OpCallHi _).
  eapply hitrace_incl_bind_a; intros.
  repeat rewrite exec_equiv_bind_bind.
  setoid_rewrite exec_equiv_bind_bind with (p1 := Atomic _).

  (* First [Op Dec] *)
  unfold Op at 4.
  rewrite atomic_equiv_bind_bind with (p1 := OpCall _).
  setoid_rewrite atomic_equiv_bind_bind with (p1 := OpExec _).

  unfold Op at 1.
  rewrite <- hitrace_incl_atomize_opcall.
  rewrite exec_equiv_bind_bind.
  setoid_rewrite exec_equiv_bind_bind.
  eapply hitrace_incl_bind_a; intros.

  rewrite <- hitrace_incl_atomize_opexec; eauto.
  setoid_rewrite exec_equiv_bind_bind with (p1 := OpExec _).
  eapply hitrace_incl_bind_a; intros.

  rewrite <- hitrace_incl_atomize_opret.
  setoid_rewrite exec_equiv_bind_bind.
  eapply hitrace_incl_bind_a; intros.

  (* Second [Op Dec] *)
  unfold Op at 3.
  rewrite atomic_equiv_bind_bind with (p1 := OpCall _).
  setoid_rewrite atomic_equiv_bind_bind with (p1 := OpExec _).

  unfold Op at 1.
  rewrite <- hitrace_incl_atomize_opcall.
  rewrite exec_equiv_bind_bind.
  setoid_rewrite exec_equiv_bind_bind.
  eapply hitrace_incl_bind_a; intros.

  rewrite <- hitrace_incl_atomize_opexec; eauto.
  setoid_rewrite exec_equiv_bind_bind with (p1 := OpExec _).
  eapply hitrace_incl_bind_a; intros.

  rewrite <- hitrace_incl_atomize_opret.
  setoid_rewrite exec_equiv_bind_bind.
  eapply hitrace_incl_bind_a; intros.

  (* Third [Op Dec] *)
  unfold Op.
  rewrite <- hitrace_incl_atomize_opcall.
  setoid_rewrite exec_equiv_bind_bind.
  eapply hitrace_incl_bind_a; intros.

  rewrite <- hitrace_incl_atomize_opexec; eauto.
  rewrite exec_equiv_bind_bind.
  eapply hitrace_incl_bind_a; intros.

  rewrite <- atomic_equiv_bind_ret with (p := OpRet _) at 2.
  rewrite <- hitrace_incl_atomize_opret.
  rewrite exec_equiv_bind_bind.
  eapply hitrace_incl_bind_a; intros.

  rewrite exec_equiv_atomicret_bind.
  reflexivity.
Qed.


(** Correctness for 1 thread *)

Theorem all_single_thread_traces_match' :
  forall T T' (p1 : proc opT opHiT T) (p2 : proc opHiT opHi2T T) (p1rest : T -> proc opT opHiT T') (p2rest : T -> proc opHiT opHi2T T'),
  (forall x, traces_match_one_thread op_step opHi_step (p1rest x) (p2rest x)) ->
  inc2_compile_ok p1 p2 ->
  traces_match_one_thread op_step opHi_step (Bind p1 p1rest) (Bind p2 p2rest).
Proof.
  intros.
  generalize dependent p2rest.
  generalize dependent p1rest.
  induction H0; intros.

  - destruct op.
    + rewrite inc_twice_atomic.

      unfold traces_match_one_thread, traces_match_ts; intros.

      exec_inv; repeat thread_inv; autorewrite with t in *.
      repeat ( exec_tid_inv; intuition try congruence ).

      exec_inv; repeat thread_inv; autorewrite with t in *.
      repeat ( exec_tid_inv; intuition try congruence ).

      exec_inv; repeat thread_inv; autorewrite with t in *.
      repeat ( exec_tid_inv; intuition try congruence ).

      repeat atomic_exec_inv.
      repeat step_inv.

      apply H in H3; deex.

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

    + rewrite dec_thrice_atomic.

      unfold traces_match_one_thread, traces_match_ts; intros.

      exec_inv; repeat thread_inv; autorewrite with t in *.
      repeat ( exec_tid_inv; intuition try congruence ).

      exec_inv; repeat thread_inv; autorewrite with t in *.
      repeat ( exec_tid_inv; intuition try congruence ).

      exec_inv; repeat thread_inv; autorewrite with t in *.
      repeat ( exec_tid_inv; intuition try congruence ).

      repeat atomic_exec_inv.
      repeat step_inv.

      apply H in H3; deex.

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

      unfold dec, dec3, state_upd; apply functional_extensionality; intros.
        destruct_ifs; omega.
      f_equal.
      unfold dec, dec3, state_upd;
        destruct_ifs; omega.

      simpl.
      replace (dec (dec s1 1) 1 1 - 1) with (s1 1 - 3).
      eauto 20.
      unfold dec, state_upd. destruct_ifs; omega.

    + unfold traces_match_one_thread, traces_match_ts; intros.

      exec_inv; repeat thread_inv; autorewrite with t in *.
      repeat ( exec_tid_inv; intuition try congruence ).

      exec_inv; repeat thread_inv; autorewrite with t in *.
      repeat ( exec_tid_inv; intuition try congruence ).

      exec_inv; repeat thread_inv; autorewrite with t in *.
      repeat ( exec_tid_inv; intuition try congruence ).

      repeat atomic_exec_inv.
      repeat step_inv.

      apply H in H3; deex.

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

      eauto.
      simpl; eauto.

  - repeat rewrite exec_equiv_ret_bind.
    eauto.

  - rewrite exec_equiv_bind_bind.
    rewrite exec_equiv_bind_bind.
    eapply IHcompile_ok.
    intros.
    eapply H1.
    eapply H2.

  - rewrite exec_equiv_ret_bind.

    unfold traces_match_one_thread, traces_match_ts in *; intros.
    eapply H in H0; deex.

    eexists; split.
    eapply ExecOne with (tid := 1).
      rewrite thread_upd_eq; auto.
      eauto.
    autorewrite with t; eauto.
    simpl; eauto.

  - rewrite exec_equiv_ret_bind.

    unfold traces_match_one_thread, traces_match_ts in *; intros.
    eapply H in H0; deex.

    eexists; split.
    eapply ExecOne with (tid := 1).
      rewrite thread_upd_eq; auto.
      eauto.
    autorewrite with t; eauto.
    simpl; eauto.
Qed.

Theorem all_single_thread_traces_match :
  forall T' (p1 : proc opT opHiT T') (p2 : proc opHiT opHi2T T'),
  inc2_compile_ok p1 p2 ->
  traces_match_one_thread op_step opHi_step p1 p2.
Proof.
  intros.
  rewrite <- exec_equiv_bind_ret with (p := p3).
  rewrite <- exec_equiv_bind_ret with (p := p4).
  eapply all_single_thread_traces_match'; eauto; intros.

  unfold traces_match_one_thread, traces_match_ts; intros.

  eapply exec_equiv_ret_None in H0.
  exec_inv; repeat thread_inv.

  eexists; split.
  eapply exec_equiv_ret_None.
  eapply ExecEmpty; eauto.
  eauto.
Qed.


(** Many-thread correctness *)

Lemma compile_ok_atomic_exec_tid : forall T (p1 : proc _ _ T) p2,
  @atomic_compile_ok _ _ opHi2T compile_op _ p1 p2 ->
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
        | inr p'' => atomic_compile_ok compile_op p' p''
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
    destruct op.

    + repeat atomic_exec_inv.
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

    + repeat atomic_exec_inv.
      repeat step_inv.
      do 2 eexists; split.
      constructor.

      replace (dec (dec (dec s1 tid) tid) tid) with (dec3 s1 tid).
      constructor.

      unfold dec, dec3, state_upd; apply functional_extensionality; intros.
        destruct_ifs; omega.

      split.
      simpl; eauto 20.

      unfold dec, dec3, state_upd;
        destruct_ifs; omega.

    + repeat atomic_exec_inv.
      repeat step_inv.
      do 2 eexists; split.
      constructor.
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
    do 2 eexists; split.
    constructor.
    split.
    simpl; eauto.
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
    simpl; eauto.
    eauto.

  - exec_tid_inv.
    do 2 eexists; split.
    constructor.
    split.
    simpl; eauto.
    eauto.
Qed.


Theorem all_traces_match_0 :
  forall ts1 (ts2 : @threads_state _ opHi2T),
  proc_match (atomic_compile_ok compile_op) ts1 ts2 ->
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
    eapply ExecEmpty; eauto.
    eauto.
Qed.


Theorem atomize_ok_preserves_trace_0 :
  forall T p1 p2,
  atomize_ok compile_op p1 p2 ->
  forall T' (p1rest p2rest : T -> proc _ _ T'),
  (forall x, hitrace_incl op_step (p1rest x) (p2rest x)) ->
  hitrace_incl op_step (Bind p1 p1rest) (Bind p2 p2rest).
Proof.
  induction 1; intros.
  - destruct op.
    + rewrite inc_twice_atomic.
      eapply hitrace_incl_bind_a.
      eauto.
    + rewrite dec_thrice_atomic.
      eapply hitrace_incl_bind_a.
      eauto.
    + unfold hicall; cbn.
      rewrite exec_equiv_bind_bind.
      setoid_rewrite exec_equiv_bind_bind.
      eapply hitrace_incl_bind_a; intros.
      unfold atomize; cbn.
      setoid_rewrite exec_equiv_bind_bind.
      rewrite exec_equiv_ret_bind.
      rewrite exec_equiv_atomicret_bind.
      eapply hitrace_incl_bind_a; intros.
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
  atomize_ok compile_op p1 p2 ->
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
  proc_match_upto n (atomize_ok compile_op) ts1 ts1' ->
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
          rewrite atomize_ok_preserves_trace; eauto.
          rewrite thread_upd_same; eauto.
          reflexivity.
    + eapply IHn.
      eapply proc_match_upto_Sn'.
      omega.
      eauto.
Qed.

Theorem atomize_ok_all_preserves_trace :
  forall ts1' ts1,
  proc_match (atomize_ok compile_op) ts1 ts1' ->
    hitrace_incl_ts op_step ts1 ts1'.
Proof.
  intros.
  eapply atomize_ok_all_upto_preserves_trace.
  eapply proc_match_upto_all.
  eauto.
Qed.

Theorem all_traces_match_1 :
  forall ts1 ts1' (ts2 : @threads_state _ opHi2T),
  proc_match (atomize_ok compile_op) ts1 ts1' ->
  proc_match (atomic_compile_ok compile_op) ts1' ts2 ->
  traces_match_ts op_step opHi_step ts1 ts2.
Proof.
  intros.
  rewrite atomize_ok_all_preserves_trace; eauto.
  eapply all_traces_match_0; eauto.
Qed.

Theorem make_one_atomic :
  forall T (p2 : proc _ opHi2T T) (p1 : proc _ _ T),
  compile_ok compile_op p1 p2 ->
    atomize_ok compile_op p1 (compile (atomize compile_op) p2) /\
    atomic_compile_ok compile_op (compile (atomize compile_op) p2) p2.
Proof.
  induction 1; simpl; intros.
  - split. constructor. repeat constructor.
  - split; constructor.
  - intuition idtac.
    constructor. eauto. intros. specialize (H1 x). intuition eauto.
    constructor. eauto. intros. specialize (H1 x). intuition eauto.
  - split; constructor.
  - split; constructor.
Qed.

Hint Resolve proc_match_cons_Proc.
Hint Resolve proc_match_cons_NoProc.


Theorem make_all_atomic :
  forall ts1 (ts2 : @threads_state _ opHi2T),
  proc_match (compile_ok compile_op) ts1 ts2 ->
  exists ts1',
    proc_match (atomize_ok compile_op) ts1 ts1' /\
    proc_match (atomic_compile_ok compile_op) ts1' ts2.
Proof.
  induction ts1; intros.
  - eapply proc_match_len in H.
    destruct ts3; simpl in *; try omega.
    eexists; split.
    eapply proc_match_nil.
    eapply proc_match_nil.
  - eapply proc_match_len in H as H'.
    destruct ts3; simpl in *; try omega.

    eapply proc_match_cons_inv in H.
    edestruct IHts1; intuition eauto.
    + exists (NoProc :: x); subst; intuition eauto.
    + repeat deex.
      edestruct (make_one_atomic H4).
      eexists (Proc _ :: x); intuition eauto.
Qed.

Theorem all_traces_match :
  forall ts1 (ts2 : @threads_state _ opHi2T),
  proc_match (compile_ok compile_op) ts1 ts2 ->
  traces_match_ts op_step opHi_step ts1 ts2.
Proof.
  intros.
  eapply make_all_atomic in H; deex.
  eapply all_traces_match_1; eauto.
Qed.