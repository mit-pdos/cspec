module Utils.Conversion
  ( module Utils.Conversion
  , module Utils.Coq ) where

import Datatypes
import Disk
import Utils.Coq

numToNat :: (Num a, Eq a) => a -> Coq_nat
numToNat n =
  case n of
    0 -> O
    _ -> S (numToNat (n-1))

type FileOffset = Integer

addrToOffset :: Coq_addr -> FileOffset
addrToOffset a = natToNum a * 4096

unit :: Coq_unit -> ()
unit _ = ()
