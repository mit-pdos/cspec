Require Import Automation.
Require Import Helpers.

Require Import SepLogic.Mem.Def.
Require Import SepLogic.Mem.Upd.
Require Import SepLogic.Pred.Def.

Definition singleton A V (a:A) (v:V) {AEQ:EqualDec A} : mem A V :=
  fun a' => if a == a' then Some v else None.

Lemma ptsto_singleton : forall `{m: mem A V} {AEQ:EqualDec A} a v,
    m |= a |-> v ->
    m = singleton a v.
Proof.
  unfold singleton; simpl; intros.
  extensionality a'.
  is_eq a a'; intuition.
Qed.

Lemma ptsto_singleton' : forall {A V} {AEQ:EqualDec A} (a:A) (v:V),
    singleton a v |= a |-> v.
Proof.
  unfold singleton; simpl; intros.
  subst.
  destruct matches; intuition.
  destruct matches; intuition.
Qed.

Theorem ptsto_valid : forall `(m: mem A V) F a v,
    m |= F * a |-> v ->
    m a = Some v.
Proof.
  intros.
  apply star_comm in H.
  simpl in *; repeat deex.
  unfold mem_union; simpl_match; auto.
Qed.

Lemma mem_disjoint_singleton : forall `{m:mem A V} {AEQ:EqualDec A} a v0 v,
    mem_disjoint (singleton a v0) m ->
    mem_disjoint (singleton a v) m.
Proof.
  unfold mem_disjoint, singleton; intuition.
  eapply H; eauto.
  destruct matches in *; eauto.
Qed.

Hint Resolve ptsto_singleton'.
Hint Resolve mem_disjoint_singleton.

Theorem ptsto_upd : forall `{m:mem A V} {AEQ:EqualDec A} F a v0 v,
    m |= F * a |-> v0 ->
    upd m a v |= F * a |-> v.
Proof.
  intros.
  apply star_comm in H.
  apply star_comm.
  cbn [pred_prop star] in *; repeat deex.
  eapply ptsto_singleton in H; eauto; subst.
  exists (singleton a v), m2; intuition eauto.
  extensionality a'.
  unfold singleton, mem_union.
  is_eq a a'; autorewrite with upd; eauto.
  is_eq a a'; autorewrite with upd; eauto.
  congruence.
Qed.
