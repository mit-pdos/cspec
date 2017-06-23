Require Import Omega.

Require Import Automation.
Require Import SepLogic.Mem.Def.
Require Import SepLogic.Mem.Upd.

(** We define [sized_domain], which specifies that a [mem nat V] has a contiguous
domain from 0 through some bound sz (that is, 0 through (sz-1) map to something,
and nothing above maps to anything).

 In addition we prove a number of properties of sized memories.
 *)

(* abbreviation for Arith's decidable < function *)
Definition lt_dec (a b:nat) : {a < b} + {~a < b} := Compare_dec.lt_dec a b.

Definition sized_domain V (m: mem nat V) sz :=
  forall a, if lt_dec a sz then
         exists v, m a = Some v
       else m a = None.

Theorem sized_domain_upd_some : forall V (m:mem nat V) sz a v0 v,
    m a = Some v0 ->
    sized_domain m sz ->
    sized_domain (upd m a v) sz.
Proof.
  unfold sized_domain; intros.
  specialize (H0 a0).
  unfold upd.
  destruct matches; repeat deex; eauto.
Qed.

Theorem sized_domain_upd_lt : forall V (m:mem nat V) sz a v,
    a < sz ->
    sized_domain m sz ->
    sized_domain (upd m a v) sz.
Proof.
  unfold sized_domain; intros.
  specialize (H0 a0).
  unfold upd.
  destruct matches; repeat deex; eauto.
Qed.

Theorem sized_domain_delete_last : forall V (m:mem nat V) sz sz',
    sz = S sz' ->
    sized_domain m sz ->
    sized_domain (delete m sz') sz'.
Proof.
  unfold sized_domain; intros; subst.
  destruct matches.
  - specialize (H0 a).
    destruct (lt_dec a (S sz')); try omega.
    deex; eexists.
    rewrite delete_neq by omega. eauto.
  - destruct (eq_nat_dec a sz'); subst.
    + rewrite delete_eq; auto.
    + rewrite delete_neq by omega.
      specialize (H0 a).
      destruct (lt_dec a (S sz')); try omega.
      auto.
Qed.

Theorem sized_domain_empty V : sized_domain (empty_mem (V:=V)) 0.
Proof.
  unfold sized_domain; intros.
  destruct (lt_dec a 0); auto.
  inversion l.
Qed.

Lemma sized_domain_not_lt : forall `(m: mem _ V) sz sz',
    sized_domain m sz ->
    sized_domain m sz' ->
    sz < sz' ->
    False.
Proof.
  intros.
  specialize (H sz).
  specialize (H0 sz).
  destruct (lt_dec sz sz); try omega.
  destruct (lt_dec sz sz'); try omega.
  repeat deex; congruence.
Qed.

Lemma sized_domain_unique_sz : forall `(m: mem _ V) sz sz',
    sized_domain m sz ->
    sized_domain m sz' ->
    sz = sz'.
Proof.
  intros.
  destruct (lt_eq_lt_dec sz sz') as [ [] | ]; auto;
    solve [ exfalso; eauto using sized_domain_not_lt ].
Qed.

Theorem sized_domain_pointwise : forall `(m: mem _ V) sz V' (f: V -> V'),
    sized_domain m sz ->
    sized_domain (fun a => match m a with
                        | Some v => Some (f v)
                        | None => None
                        end) sz.
Proof.
  unfold sized_domain; intros.
  specialize (H a).
  destruct matches; repeat simpl_match; eauto.
  repeat deex; congruence.
Qed.
