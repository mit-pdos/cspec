(** uncomment for interactive usage *)
(* Cd "../../". *)
Cd "replicate-nbd/src/".

Extraction Language Haskell.

Require Import Bytes.

Extract Constant bytes => "BS.ByteString".
Extract Constant bytes_eqb => "(\n b1 b2 -> if b1 Prelude.== b2 then Datatypes.Coq_true else Datatypes.Coq_false)".
Extract Constant bytes0 => "(\n -> BS.replicate (natToInt n) 0)".

(* TODO: add the following to the imports of Bytes:

import CoqUtils
import qualified Data.ByteString as BS
 *)

Require Import ReplicatedDisk.
Recursive Extraction Library ReplicatedDisk.

(* this appears to be needed to compile this file *)
Cd "../../".
