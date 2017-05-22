{-# LANGUAGE Rank2Types #-}
module Replication.ReplicatedDiskImpl where

import           Control.Monad (unless)
import qualified Data.ByteString as BS
import           ReplicatedDisk
import           Replication.TwoDiskEnvironment (TwoDiskProg)
import           SeqDiskAPI
import           TwoDiskImpl (_TD__td)
import           Utils.Conversion

-- TODO: use newtype for block things

type BlockOffset = Int
type ByteOffset = Int

-- |wrapper for replicated disk Read
rdRead :: BlockOffset -> TwoDiskProg BS.ByteString
rdRead off = _RD__prim _TD__td $ D__Read (fromIntegral off)

-- |wrapper for replicated disk Write
rdWrite :: BlockOffset -> BS.ByteString -> TwoDiskProg ()
rdWrite off dat = _RD__prim _TD__td $ D__Write (fromIntegral off) dat

-- |read multiple blocks by calling rdRead and concatenating the results
readBytes :: ByteOffset -> Int -> TwoDiskProg BS.ByteString
readBytes off len =
  if not (off `mod` blocksize == 0 && len `mod` blocksize == 0) then
    error $ "misaligned read at " ++ show off ++ " length " ++ show len
  else BS.concat <$> mapM rdRead [0..len `div` blocksize-1]

-- |write a chunk of data by calling rdWrite for each block
-- (assumes the string is an integer number of blocks long)
writeBytes :: ByteOffset -> BS.ByteString -> TwoDiskProg ()
writeBytes off dat =
  if not (off `mod` blocksize == 0 && BS.length dat `mod` blocksize == 0) then
    error $ "misaligned write at " ++ show off ++ " length " ++ show (BS.length dat)
  else loop (off `div` blocksize) dat
  where loop blockOff s = unless (BS.length s == 0) $
          let (b, rest) = BS.splitAt blocksize s in do
            rdWrite blockOff b
            loop (blockOff+1) rest

-- |wrapper for replicated disk recovery procedure
recover :: TwoDiskProg ()
recover = _RD__recover _TD__td
