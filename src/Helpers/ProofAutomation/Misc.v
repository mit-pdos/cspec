Require Import Arith.
Require Import Bool.
Require Import List.
Require Import String.
Require Import Eqdep.

Require Import ProofAutomation.Propositional.

(** ** Other proof automation helpers *)

Ltac sigT_eq :=
  match goal with
  | [ H: existT ?P ?a _ = existT ?P ?a _ |- _ ] =>
    apply Eqdep.EqdepTheory.inj_pair2 in H; subst
  end.

Ltac inv_clear H := inversion H; clear H; subst; repeat sigT_eq.

(** substitute variables that are let bindings (these can be created with [set
(x:=value)] and appear in the context as [v := def]) *)
Ltac subst_var :=
  repeat match goal with
  | [ v := _ |- _ ] => subst v
  end.

Create HintDb false.

Ltac solve_false :=
  solve [ exfalso; eauto with false ].

Ltac rename_by_type type name :=
  match goal with | x : type |- _ => rename x into name end.

Ltac induct H :=
  induction H; repeat sigT_eq; propositional.
Ltac invert H :=
  inversion H; repeat sigT_eq; propositional; repeat sigT_eq.

Ltac is_one_goal := let n := numgoals in guard n = 1.
