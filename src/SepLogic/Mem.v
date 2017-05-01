Require Export EquivDec.
Require Export FunctionalExtensionality.
Require Import Automation.

Set Implicit Arguments.

Definition mem A {AEQ:EqDec A eq} V := A -> option V.
Arguments mem A {AEQ} V.

Section Memories.

  Variable A:Type.
  Context {AEQ:EqDec A eq}.
  Variable V:Type.

  Implicit Type (m:mem A V).

  Definition upd m a v : mem A V :=
    fun a' => if AEQ a a' then Some v else m a'.

  Theorem upd_eq : forall m a v,
      upd m a v a = Some v.
  Proof.
    unfold upd; intros.
    destruct matches.
  Qed.

  Theorem upd_neq : forall m a v a',
      a <> a' ->
      upd m a v a' = m a'.
  Proof.
    unfold upd; intros.
    destruct matches.
  Qed.

  Theorem upd_upd : forall m a v v',
      upd (upd m a v) a v' = upd m a v'.
  Proof.
    unfold upd; intros.
    extensionality a'.
    destruct matches.
  Qed.

End Memories.

Definition empty_mem {A AEQ V} : @mem A AEQ V := fun _ => None.

Hint Rewrite upd_eq : upd.
Hint Rewrite upd_upd : upd.
Hint Rewrite upd_neq using (solve [ auto ]) : upd.

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
