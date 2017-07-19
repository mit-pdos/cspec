Require Import Helpers.
Require Import Omega.

(* Very basic definitions for modeling disks. *)

Definition addr := nat.

(* We introduce this definition to make the large constant opaque, for
performance reasons. *)
Definition blockbytes := 1024.
Opaque blockbytes.

Definition block := bytes blockbytes.
Definition block0 : block := bytes0 blockbytes.

(* To deal with Coq v8.6 not having https://github.com/coq/coq/pull/876 yet *)
Local Ltac omega_orig := omega.
Ltac omega := unfold addr in *; omega_orig.
