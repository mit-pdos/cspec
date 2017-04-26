Require Import Bytes.
Require Import Mem.

Definition addr := nat.
Definition block := bytes 4096.

Definition disk := mem addr block.
