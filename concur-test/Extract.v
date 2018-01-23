Cd "concur-test/extract/".

Require Import ExtrHaskellBasic.
Require Import ExtrHaskellNatInteger.

Extraction Language Haskell.

Require Import Spec.Example2.

Separate Extraction compiled_threads.

Cd "../../".
