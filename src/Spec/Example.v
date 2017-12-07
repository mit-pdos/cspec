Require Import Helpers.Helpers.
Require Import Helpers.ListStuff.
Require Import ConcurProc.

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
