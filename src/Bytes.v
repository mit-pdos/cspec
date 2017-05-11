(** Bytes is an axiomatic library for byte strings. *)

Require Import EquivDec.

Set Implicit Arguments.

(* bytes n is a byte string with length n. *)
Parameter bytes : nat -> Type.

Parameter bytes_dec : forall n, EqDec (bytes n) eq.

Axiom bytes0 : forall n, bytes n.
