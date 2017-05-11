(** Bytes is an axiomatic library for byte strings. *)

Require Import EquivDec.

Set Implicit Arguments.

(* bytes n is a byte string with length n. *)
Parameter bytes : nat -> Type.

Parameter bytes_eqb : forall n, bytes n -> bytes n -> bool.

Axiom bytes_eqb_correct : forall n (b1 b2:bytes n),
    bytes_eqb b1 b2 = true <-> b1 = b2.

Instance bytes_dec n : EqDec (bytes n) eq.
Proof.
  hnf; intros.
  unfold equiv, complement.
  destruct (bytes_eqb x y) eqn:?.
  - left.
    apply bytes_eqb_correct; auto.
  - right; intro.
    apply bytes_eqb_correct in H; congruence.
Defined.

Axiom bytes0 : forall n, bytes n.
