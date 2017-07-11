module Utils.Conversion where

import Sectors

-- size of a block in bytes
blocksize :: Num a => a
blocksize = fromIntegral blockbytes

type FileOffset = Integer

addrToOffset :: Coq_addr -> FileOffset
addrToOffset a = a * blockbytes
