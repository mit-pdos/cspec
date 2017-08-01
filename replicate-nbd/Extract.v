Cd "replicate-nbd/extract/".

Require Import ExtrHaskellNatInteger.
Require Import ExtrHaskellBasic.
Require Import Helpers.ExtrBytes.
Require Import Refinement.ExtrProg.

Extraction Language Haskell.

Require Import Lab4.ReplicatedServer.

Separate Extraction diskSize serverLoop init.

Cd "../../".
