Require Import Refinement.Prog.

Extraction Language Haskell.

Extract Constant opT "a" => "()".
Extract Constant world => "()".

Extract Inductive proc => "TheProc"
                           ["prim_error" "return" "(>>=)"]
                           "(\fprim fret fbind -> error 'pattern match on proc')".
