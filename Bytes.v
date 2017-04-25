Require Import DecidableEquality.
(** Bytes is an axiomatic library for byte strings. *)

(* bytes n is a byte string with length n. *)
Axiom bytes : nat -> Type.

Axiom bytes_dec : forall n, EqDec (bytes n).

Existing Instance bytes_dec.
