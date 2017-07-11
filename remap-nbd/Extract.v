Cd "remap-nbd/src/".

Require Import ExtrHaskellBasic.
Require Import ExtrHaskellNatInteger.
Require Import ExtrBytes.
Require Import Refinement.ProgLang.ExtrProg.
Require Import BadSectorDisk.ExtrBadSectorDisk.

Extraction Language Haskell.

Require Import RemappedDisk.Server.

Extract Inlined Constant Compare_dec.lt_dec => "((Prelude.<) :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool)".

Separate Extraction serverLoop init diskSize.

Cd "../../".
