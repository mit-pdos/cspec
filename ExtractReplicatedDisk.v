Cd "replicate-nbd/src/".

Require Import ExtrHaskellNatInteger.
Require Import ExtrBytes.

Extraction Language Haskell.

Require Import ReplicatedDisk.
Separate Extraction RD.Read RD.Write RD.Recover.

Cd "../../".
