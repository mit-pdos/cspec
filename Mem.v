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

Hint Rewrite upd_eq : upd.
Hint Rewrite upd_upd : upd.
Hint Rewrite upd_neq using (solve [ auto ]) : upd.
