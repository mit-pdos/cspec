(** uncomment for interactive usage *)
(* Cd "../../". *)
Cd "replicate-nbd/src/ReplicatedDisk/".

Extraction Language Haskell.

Require Import Bytes.

Extract Constant bytes => "BS.ByteString".
Extract Constant bytes_eqb => "(=)".
Extract Constant bytes0 => "(\n -> BS.replicate n 0)".

Require Import ReplicatedDisk.
Recursive Extraction Library ReplicatedDisk.

(* this appears to be needed to compile this file *)
Cd "../../../".
