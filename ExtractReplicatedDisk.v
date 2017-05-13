Cd "replicate-nbd/src/".

Extraction Language Haskell.

Require Import ExtrHaskellNatInteger.
Require Import Bytes.

Extract Constant bytes => "BS.ByteString".
Extract Constant bytes_dec => "(\n b1 b2 -> if b1 Prelude.== b2 then Specif.Coq_left else Specif.Coq_right)".
Extract Constant bytes0 => "(\n -> BS.replicate (Prelude.fromIntegral n) 0)".

(* TODO: add the following to the imports of Bytes:

import qualified Specif
import qualified Data.ByteString as BS
import CoqUtils
 *)

Require Import ReplicatedDisk.
Separate Extraction RD.Read RD.Write RD.Recover.

Cd "../../".
