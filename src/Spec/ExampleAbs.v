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
Require Import Abstraction.

Import ListNotations.

Global Set Implicit Arguments.
Global Generalizable All Variables.


(** Opcodes *)

Inductive opLoT : Type -> Type :=
| Inc : opLoT nat
| Dec : opLoT nat.

Variable opHiT : Type -> Type.


(** State *)

Record State1 := mkState {
  Value : nat;
  Lock : option nat;
}.

Definition State2 := nat.


(** Semantics *)

Inductive op_step1 : forall T, opLoT T -> nat -> State1 -> T -> State1 -> Prop :=
| StepInc1 : forall tid v,
  op_step1 Inc tid (mkState v None) v (mkState (v + 1) None)
| StepDec1 : forall tid v,
  op_step1 Dec tid (mkState v None) v (mkState (v - 1) None).

Inductive op_step2 : forall T, opLoT T -> nat -> State2 -> T -> State2 -> Prop :=
| StepInc2 : forall tid v,
  op_step2 Inc tid v v (v + 1)
| StepDec2 : forall tid v,
  op_step2 Dec tid v v (v - 1).

Hint Extern 1 (op_step1 _ _ _ _ _) => econstructor.
Hint Extern 1 (op_step2 _ _ _ _ _) => econstructor.

Ltac step_inv :=
  match goal with
  | H : op_step1 _ _ _ _ _ |- _ =>
    inversion H; clear H; subst; repeat sigT_eq
  | H : op_step2 _ _ _ _ _ |- _ =>
    inversion H; clear H; subst; repeat sigT_eq
  end.


(** Abstraction relation *)

Definition absR (s1 : State1) (s2 : State2) :=
  Lock s1 = None /\
  Value s1 = s2.

Ltac absR_inv :=
  match goal with
  | H : absR _ _ |- _ =>
    inversion H; clear H; subst; repeat sigT_eq
  end.

Theorem absR_ok :
  op_abs absR op_step1 op_step2.
Proof.
  unfold op_abs; intros.
  destruct s1; absR_inv.
  simpl in *; subst.
  unfold absR.
  destruct op; step_inv.
  all: eexists; intuition eauto.
Qed.

Hint Resolve absR_ok.


(** Trace inclusion *)

Theorem sanity_check :
  forall s1 s2 (ts : @threads_state opLoT opHiT) tr,
    absR s1 s2 ->
    exec_prefix op_step1 s1 ts tr ->
    exec_prefix op_step2 s2 ts tr.
Proof.
  intros.
  eapply trace_incl_abs; eauto.
Qed.
