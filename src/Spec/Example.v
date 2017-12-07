Require Import Helpers.Helpers.
Require Import Helpers.ListStuff.
Require Import ConcurProc.
Require Import Equiv.
Require Import Omega.

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
