Require Import TwoDisk.TwoDiskOps.
Require Import TwoDisk.TwoDiskImpl.

Extraction Language Haskell.

Extract Constant read => "TD.read".
Extract Constant write => "TD.write".
Extract Constant sync => "TD.sync".
Extract Constant diskSize => "TD.diskSize".

Extract Constant TwoDiskImpl.TD.abstr => "Hoare.Build_LayerAbstraction".
