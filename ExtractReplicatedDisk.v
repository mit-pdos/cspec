Cd "replicate-nbd/src/".

Require Import ExtrHaskellNatInteger.
Require Import ExtrHaskellBasic.
Require Import ExtrBytes.
Require Import Refinement.ProgLang.ExtrProg.
Require Import Refinement.ExtrTwoDiskImpl.

Extraction Language Haskell.

Require Import ReplicatedDisk.
Require Import Refinement.TwoDiskImpl.

Separate Extraction TD.td RD.prim RD.recover.

Cd "../../".
