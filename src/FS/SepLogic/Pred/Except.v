Require Import POCS.

Require Import EquivDec.
Require Import FS.SepLogic.Mem.Def.
Require Import FS.SepLogic.Mem.Upd.
Require Import FS.SepLogic.Pred.Def.

Definition pred_except `(F: pred A V) {AEQ: EqDec A eq} a v : pred A V :=
  mkPred (fun m => upd m a v |= F).

Definition pred_eexcept `(F: pred A V) {AEQ: EqDec A eq} a : pred A V :=
  mkPred (fun m => exists v, upd m a v |= F).

Definition mem_except `(m: mem A V) {AEQ: EqDec A eq} a : mem A V :=
  fun a' => if a == a' then None
         else m a'.

Theorem pred_except_ptsto : forall `(F: pred A V) {AEQ: EqDec A eq} a v,
    pred_except F a v * a |-> v ===> F.
Proof.
  intros.
  rewrite star_comm.
  unfold pimpl, pred_except; simpl; intros.
  repeat deex.
  replace (mem_union m1 m2) with (upd m2 a v); eauto.
  extensionality a'.
  unfold mem_union, upd.
  admit.
(*
  destruct (m2 a') eqn:?; try solve_false.
  simpl_match; eauto.
  rewrite H3; auto.
*)
Admitted.

Axiom pred_eexcept_ptsto_eq : forall {A V} {AEQ: EqDec A eq} a (v : V),
  pred_eexcept (a |-> v) a ===> emp.
Axiom pred_eexcept_ptsto_ne : forall {A V} {AEQ: EqDec A eq} a' a (v : V),
  a <> a' ->
  pred_eexcept (a |-> v) a' ===> a |-> v.
Axiom pred_eexcept_star : forall `(p1: pred A V) p2 {AEQ: EqDec A eq} a',
  pred_eexcept (p1 * p2) a' ===> pred_eexcept p1 a' * pred_eexcept p2 a'.

Theorem pred_extract_merge : forall {A V} {AEQ: EqDec A eq} m F0 F1 a (v : V),
  m |= F0 * a |-> v ->
  m |= F1 ->
  m |= (pred_eexcept F1 a) * a |-> v.
Admitted.

Theorem pred_merge_eq : forall {A V} {AEQ: EqDec A eq} m F0 F1 (a : A) (v0 v1 : V),
  m |= F0 * a |-> v0 ->
  m |= F1 * a |-> v1 ->
  v0 = v1.
Admitted.
