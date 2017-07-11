Require Import Arith.
Require Import Bool.

Class EqualDec A :=
  equal_dec : forall x y : A, { x = y } + { x <> y }.

Notation " x == y " := (equal_dec (x :>) (y :>)) (no associativity, at level 70).

Instance nat_equal_dec : EqualDec nat := eq_nat_dec.
Instance bool_equal_dec : EqualDec bool := bool_dec.
