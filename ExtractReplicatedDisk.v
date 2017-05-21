Cd "replicate-nbd/src/".

Require Import ExtrHaskellNatInteger.
Require Import ExtrHaskellBasic.
Require Import ExtrBytes.
Require Import Shallow.ProgLang.ExtrProg.
Require Import Shallow.ExtrTwoDiskImpl.

Extraction Language Haskell.

Require Import ReplicatedDisk.
Require Import Shallow.TwoDiskImpl.

Separate Extraction TD.td RD.prim RD.recover.

Cd "../../".
