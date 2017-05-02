Require Import EquivDec.

Require Import Automation.

Require Import SepLogic.Mem.Def.
Require Import SepLogic.Pred.Def.
Require Import SepLogic.Pred.Ptsto.

Definition insert `(m: mem A V) {AEQ: EqDec A eq} a v : mem A V :=
  fun a' => if a == a' then
           match m a with
           | None => Some v
           | Some _ => m a'
           end else m a'.

Definition pred_except `(F: pred A V) {AEQ: EqDec A eq} a v : pred A V :=
  mkPred (fun m => F (insert m a v)).

Definition mem_except `(m: mem A V) {AEQ: EqDec A eq} a : mem A V :=
  fun a' => if a == a' then
           None
         else m a'.

Theorem pred_except_ptsto : forall `(F: pred A V) {AEQ: EqDec A eq} a v,
    pred_except F a v * a |-> v ===> F.
Proof.
  intros.
  rewrite star_comm.
  unfold pimpl, pred_except; simpl; intros.
  repeat deex.
  replace (mem_union m1 m2) with (insert m2 a v); eauto.
  extensionality a'.
  unfold insert, mem_union.
  is_eq a a'.
  destruct (m2 a') eqn:?; try solve_false.
  simpl_match; eauto.
  rewrite H3; auto.
Qed.
