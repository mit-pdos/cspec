Require Import Refinement.Prog.
Require Import Refinement.Hoare.

Axiom cannot_crash : can_crash = False.

Ltac cannot_crash' :=
  exfalso;
  match goal with
  | H: can_crash |- _ => rewrite cannot_crash in H; exact H
  end.

Theorem exec_cannot_crash : forall T (p : prog T) w w',
  exec p w (Crashed w') -> False.
Proof.
  intros.
  remember (Crashed w') as cw.
  induction H; try congruence; cannot_crash'.
Qed.

Theorem always_rec_noop : forall R State rec_impl abstr effect,
  rec_noop (R := R) (State := State) rec_impl abstr effect.
Proof.
  unfold rec_noop; simpl; intros.
  unfold prog_spec; simpl; intros.
  inv_rexec; inv_ret; eauto.
  cannot_crash'.
Qed.

Ltac cannot_crash :=
  repeat match goal with
  | H: can_crash |- _ => exfalso; rewrite cannot_crash in H; exact H
  | H: exec _ _ (Crashed _) |- _ => exfalso; apply exec_cannot_crash in H; exact H
  | |- rec_noop _ _ _ => apply always_rec_noop
  end.
