(** Bytes is an axiomatic library for byte strings. *)

Require Import EquivDec.

(* bytes n is a byte string with length n. *)
Axiom bytes : nat -> Type.

Axiom bytes_dec : forall n, EqDec (bytes n) eq.

Existing Instance bytes_dec.
