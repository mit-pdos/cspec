Require Import POCS.

Require Import EquivDec.
Require Import FS.SepLogic.Mem.Def.
Require Import FS.SepLogic.Mem.Upd.
Require Import FS.SepLogic.Pred.Def.
Require Import FS.SepLogic.Pred.MemIs.
Require Import FS.SepLogic.Pred.Ptsto.
Require Import FS.SepLogic.Pred.Except.

Theorem mem_is_except : forall `(m: mem A V) {AEQ:EqDec A eq} a v,
    m a = Some v ->
    m |= pred_except (mem_is m) a v * a |-> v.
Proof.
  intros.
  apply star_comm.
  cbn [pred_prop pred_except star]; intros.
  exists (singleton a v), (mem_except m a); intuition.
(*
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
*)
Admitted.

Theorem mem_is_upd : forall `(m: mem A V) {AEQ:EqDec A eq} a v v',
    pred_except (mem_is m) a v ===>
                pred_except (mem_is (upd m a v')) a v'.
Proof.
  unfold pimpl, pred_except; simpl; intros; subst.
  extensionality a'.
  unfold upd, upd in *.
(*
  is_eq a a'; eauto.
Qed.
*)
Admitted.
