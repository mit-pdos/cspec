Cd "replicate-nbd/src/".

Require Import ExtrHaskellNatInteger.
Require Import ExtrHaskellBasic.
Require Import Helpers.ExtrBytes.
Require Import Refinement.ExtrProg.
Require Import TwoDisk.ExtrTwoDisk.

Extraction Language Haskell.

Require Import ReplicatedDisk.Server.

Separate Extraction diskSize serverLoop init.

Cd "../../".
