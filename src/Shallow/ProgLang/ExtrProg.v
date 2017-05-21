Require Import Shallow.ProgLang.Prog.

Extraction Language Haskell.

Extract Constant opT "a" => "()".
Extract Constant world => "()".

Extract Inductive prog => "ReaderT Config IO"
                           ["prim_error" "return" "(>>=)"]
                           "(\fprim fret fbind -> error 'pattern match on prog')".
