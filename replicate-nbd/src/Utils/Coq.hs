module Utils.Coq where

import qualified Datatypes

natToNum :: Num a => Datatypes.Coq_nat -> a
natToNum n =
  case n of
    Datatypes.O -> 0
    Datatypes.S n' -> 1+natToNum n'
