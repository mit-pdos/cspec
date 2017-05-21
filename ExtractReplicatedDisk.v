Cd "replicate-nbd/src/".

Require Import ExtrHaskellNatInteger.
Require Import ExtrBytes.
Require Import Shallow.ProgLang.ExtrProg.
Require Import Shallow.ExtrTwoDiskImpl.

Extraction Language Haskell.

Require Import ReplicatedDisk.
Require Import Shallow.TwoDiskImpl.

Separate Extraction RD.Read RD.Write RD.Recover TD.td.

Cd "../../".
