Require Import Shallow.TwoDiskImpl.

Extraction Language Haskell.

Extract Constant TD.read => "TD.read".
Extract Constant TD.write => "TD.write".
Extract Constant TD.diskSize => "TD.diskSize".

Extract Constant TD.refinement => "unsafeCoerce".
