Require Import Helpers.
Require Import Automation.
Require Import SepLogic.Mem.Def.

Section Upd.

  Variable A:Type.
  Context {AEQ:EqualDec A}.
  Variable V:Type.

  Implicit Type (m:mem A V).

  Definition upd m a v : mem A V :=
    fun a' => if a == a' then Some v else m a'.

  Definition delete m a : mem A V :=
    fun a' => if a == a' then None else m a'.

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

  Theorem delete_eq : forall m a,
      delete m a a = None.
  Proof.
    unfold delete; intros.
    destruct matches.
  Qed.

  Theorem delete_neq : forall m a a',
      a <> a' ->
      delete m a a' = m a'.
  Proof.
    unfold delete; intros.
    destruct matches.
  Qed.

End Upd.

Hint Rewrite upd_eq : upd.
Hint Rewrite delete_eq : upd.
Hint Rewrite upd_upd : upd.
Hint Rewrite upd_neq using (solve [ auto || congruence ]) : upd.
Hint Rewrite delete_neq using (solve [ auto || congruence ]) : upd.
