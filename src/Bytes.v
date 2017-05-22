(** Bytes is an axiomatic library for byte strings. *)

Require Import EquivDec.

Set Implicit Arguments.

(* bytes n is a byte string with length n. *)
Parameter bytes : nat -> Type.

Parameter bytes_dec : forall n, EqDec (bytes n) eq.

Axiom bytes0 : forall n, bytes n.

Axiom bconcat : forall n1 n2, bytes n1 -> bytes n2 -> bytes (n1+n2).

Axiom bsplit : forall n1 n2, bytes (n1+n2) -> bytes n1 * bytes n2.

Arguments bsplit {n1 n2} bs.
