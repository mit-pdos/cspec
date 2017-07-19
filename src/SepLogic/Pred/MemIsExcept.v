Require Import Automation.
Require Import Helpers.

Require Import SepLogic.Mem.Def.
Require Import SepLogic.Mem.Upd.
Require Import SepLogic.Pred.Def.
Require Import SepLogic.Pred.MemIs.
Require Import SepLogic.Pred.Ptsto.
Require Import SepLogic.Pred.Except.

Theorem mem_is_except : forall `(m: mem A V) {AEQ:EqualDec A} a v,
    m a = Some v ->
    m |= pred_except (mem_is m) a v * a |-> v.
Proof.
  intros.
  apply star_comm.
  cbn [pred_prop pred_except star]; intros.
  exists (singleton a v), (mem_except m a); intuition.
  eapply mem_is_eq.
  extensionality a'.
  unfold upd, mem_except.
  is_eq a a'; eauto.

  unfold mem_disjoint, singleton, mem_except; intros.
  is_eq a a0; congruence.

  extensionality a'.
  unfold mem_union, singleton, mem_except.
  is_eq a a'; eauto.
Qed.

Theorem mem_is_upd : forall `(m: mem A V) {AEQ:EqualDec A} a v v',
    pred_except (mem_is m) a v ===>
                pred_except (mem_is (upd m a v')) a v'.
Proof.
  unfold pimpl, pred_except; simpl; intros; subst.
  extensionality a'.
  unfold upd, upd in *.
  is_eq a a'; eauto.
Qed.
