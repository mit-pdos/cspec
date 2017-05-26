Require Import Bytes.

(* Very basic definitions for modeling disks. *)

Definition addr := nat.

(* We introduce this definition to make the large constant opaque, for
performance reasons. *)
Definition blockbytes := 1024.
Opaque blockbytes.

Definition block := bytes blockbytes.
Definition block0 : block := bytes0 blockbytes.
