Require Import Shallow.TwoDiskImpl.

Extraction Language Haskell.

(* TODO: move these operations to a separate TwoDiskOps file, import it
qualified as TD, and then use TD.read/TD.write/TD.diskSize here *)
Extract Constant TD.read => "tdRead".
Extract Constant TD.write => "tdWrite".
Extract Constant TD.diskSize => "tdDiskSize".

Extract Constant TD.refinement => "unsafeCoerce".
