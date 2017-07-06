Cd "statdb-cli/src/".

Require Import ExtrHaskellBasic.
Require Import ExtrHaskellNatInteger.
Require Import Refinement.ProgLang.ExtrProg.
Require Import Variables.ExtrVariables.

Extraction Language Haskell.

Require Import StatDb.StatDbCli.

Extract Inlined Constant PeanoNat.Nat.div => "(\n m -> if m Prelude.== 0 then 0 else Prelude.div n m)".

Separate Extraction cli.

Cd "../../".
