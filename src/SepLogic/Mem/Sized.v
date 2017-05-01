Require Arith.

Require Import Automation.
Require Import SepLogic.Mem.Def.
Require Import SepLogic.Mem.Upd.

Definition lt_dec (a b:nat) : {a < b} + {~a < b}.
Proof.
  apply Compare_dec.lt_dec.
Defined.

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

Theorem sized_domain_empty V : sized_domain (empty_mem (V:=V)) 0.
Proof.
  unfold sized_domain; intros.
  destruct (lt_dec a 0); auto.
  inversion l.
Qed.
