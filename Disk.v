Require Import Bytes.
Require Export Mem.

Definition addr := nat.

(* We introduce this definition to make the large constant opaque, for
performance reasons. *)
Definition fourkilobytes := 4096.
Opaque fourkilobytes.
Definition block := bytes fourkilobytes.

Definition disk := mem addr block.
