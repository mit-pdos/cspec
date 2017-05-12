module Utils.Coq where

import qualified Datatypes

natToInt :: Datatypes.Coq_nat -> Int
natToInt n =
  case n of
    Datatypes.O -> 0
    Datatypes.S n' -> 1+natToInt n'
