{-# LANGUAGE Rank2Types #-}
module Replication.Interpreter where

import qualified Data.ByteString as BS
import           Prog
import           System.IO
import           TwoDiskProg
import           Unsafe.Coerce
import           Utils.Conversion

type Interpreter = forall t. TD__Coq_prog t -> IO t

data Config =
  Config { disk0 :: Handle
         , disk1 :: Handle }

newConfig :: FilePath -> FilePath -> IO Config
newConfig fn0 fn1 =
  Config <$>
    openBinaryFile fn0 ReadWriteMode <*>
    openBinaryFile fn1 ReadWriteMode

diskSizes :: Config -> IO (Integer, Integer)
diskSizes c = (,) <$> hSize (disk0 c) <*> hSize (disk1 c)

pread :: Handle -> Int -> FileOffset -> IO BS.ByteString
pread h len off = do
  hSeek h AbsoluteSeek off
  BS.hGet h len

pwrite :: Handle -> BS.ByteString -> FileOffset -> IO ()
pwrite h dat off = do
  hSeek h AbsoluteSeek off
  BS.hPut h dat

hSize :: Handle -> IO FileOffset
hSize h = do
  hSeek h SeekFromEnd 0
  hTell h

closeConfig :: Config -> IO ()
closeConfig c = do
  hClose (disk0 c)
  hClose (disk1 c)

interpreter :: Config -> Interpreter
interpreter c = interp
  where
    getDisk :: Coq_diskId -> Handle
    getDisk Coq_d0 = disk0 c
    getDisk Coq_d1 = disk1 c

    interp :: Interpreter
    interp (Prim op) = case op of
      -- TODO: catch exceptions and return Failed
      TD__Read d a -> do
        b <- pread (getDisk d) blocksize (addrToOffset a)
        return $ unsafeCoerce (Working (b::BS.ByteString))
      TD__Write d a b -> do
        pwrite (getDisk d) b (addrToOffset a)
        return $ unsafeCoerce (Working ())
      TD__DiskSize d -> do
        sz <- hSize (getDisk d)
        return $ unsafeCoerce (Working (sz `div` blocksize::Integer))
    interp (Ret t) = return t
    interp (Bind p1 p2) = do
      r <- interp p1
      interp (p2 r)
