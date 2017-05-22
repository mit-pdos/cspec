Cd "replicate-nbd/src/".

Require Import ExtrHaskellNatInteger.
Require Import ExtrHaskellBasic.
Require Import ExtrBytes.
Require Import Refinement.ProgLang.ExtrProg.
Require Import TwoDisk.ExtrTwoDiskImpl.

Extraction Language Haskell.

Require Import SeqDisk.ReplicatedDisk.
Require Import TwoDisk.TwoDiskImpl.

Separate Extraction TD.td RD.prim RD.recover.

Cd "../../".
