Require Import Refinement.Prog.

Extraction Language Haskell.

Extract Constant opT "a" => "()".
Extract Constant world => "()".

Extract Inductive prog => "TheProg"
                           ["prim_error" "return" "(>>=)"]
                           "(\fprim fret fbind -> error 'pattern match on prog')".
