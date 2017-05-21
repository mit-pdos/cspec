module Utils.Conversion where

import Datatypes
import Disk

-- size of a block in bytes
blocksize :: Num a => a
blocksize = fromIntegral blockbytes

type FileOffset = Integer

addrToOffset :: Coq_addr -> FileOffset
addrToOffset a = a * blockbytes

unit :: Coq_unit -> ()
unit _ = ()

coqTt :: () -> Coq_unit
coqTt _ = Coq_tt
