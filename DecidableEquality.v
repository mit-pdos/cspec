Definition EqDec A := forall (x y:A), {x=y}+{x<>y}.
Existing Class EqDec.

Instance unit_eq_dec : EqDec unit.
Proof.
  hnf; intros.
  left.
  destruct x, y; auto.
Defined.

Instance nat_eq_dec : EqDec nat.
Proof.
  hnf; intros.
  decide equality.
Defined.

Instance bool_eq_dec : EqDec bool.
Proof.
  hnf; intros.
  decide equality.
Defined.

Definition is_eq {A} {eq_dec:EqDec A} x y := eq_dec x y.
