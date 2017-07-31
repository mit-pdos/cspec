Cd "remap-nbd/src/".

Require Import ExtrHaskellBasic.
Require Import ExtrHaskellNatInteger.
Require Import Helpers.ExtrBytes.
Require Import Refinement.ExtrProg.

Extraction Language Haskell.

Require Import RemappedDisk.RemappedServer.

Extract Inlined Constant Compare_dec.lt_dec => "((Prelude.<) :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool)".

Separate Extraction serverLoop init diskSize.

Cd "../../".
