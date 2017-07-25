Require Import Helpers.
Require Import Omega.

(* Very basic definitions for modeling disks. *)

Definition addr := nat.

(* We introduce this definition to make the large constant opaque, for
performance reasons. *)
Definition blockbytes := 1024.

Definition block := bytes blockbytes.
Definition block0 : block := bytes0 _.
Definition block1 : block := bytes1 _.

Theorem block0_block1_differ : block0 <> block1.
Proof.
  apply bytes_differ.
Qed.

Hint Resolve block0_block1_differ.

(* To deal with Coq v8.6 not having https://github.com/coq/coq/pull/876 yet *)
Local Ltac omega_orig := omega.
Ltac omega := unfold addr in *; omega_orig.

Opaque blockbytes.
