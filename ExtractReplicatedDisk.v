Cd "replicate-nbd/src/".

Require Import ExtrHaskellNatInteger.
Require Import ExtrHaskellBasic.
Require Import ExtrBytes.
Require Import Refinement.ProgLang.ExtrProg.
Require Import TwoDisk.ExtrTwoDiskImpl.

Extraction Language Haskell.

Require Import NBD.Server.
Require Import NBD.ExtrServer.

Separate Extraction serverLoop init.

Cd "../../".
