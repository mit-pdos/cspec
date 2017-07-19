Require Import Automation.
Require Import Helpers.

Require Import SepLogic.Mem.Def.
Require Import SepLogic.Mem.Upd.
Require Import SepLogic.Pred.Def.

Definition pred_except `(F: pred A V) {AEQ: EqualDec A} a v : pred A V :=
  mkPred (fun m => upd m a v |= F).

Definition mem_except `(m: mem A V) {AEQ: EqualDec A} a : mem A V :=
  fun a' => if a == a' then None
         else m a'.

Theorem pred_except_ptsto : forall `(F: pred A V) {AEQ: EqualDec A} a v,
    pred_except F a v * a |-> v ===> F.
Proof.
  intros.
  rewrite star_comm.
  unfold pimpl, pred_except; simpl; intros.
  repeat deex.
  replace (mem_union m1 m2) with (upd m2 a v); eauto.
  extensionality a'.
  unfold mem_union, upd.
  is_eq a a'.
  destruct (m2 a') eqn:?; try solve_false.
  simpl_match; eauto.
  rewrite H3; auto.
Qed.
