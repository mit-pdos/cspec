{-# LANGUAGE Rank2Types #-}
module Replication.ReplicatedDiskImpl where

import           ArrayAPI
import qualified Data.ByteString as BS
import           ReplicatedDisk
import           Replication.TwoDiskEnvironment (TwoDiskProg)
import           TwoDiskImpl (_TD__td)
import           Utils.Conversion

-- TODO: use newtype for block things

type BlockOffset = Int
type ByteOffset = Int

-- |wrapper for Array read that checks for invalid parameters and converts types
readBytes :: ByteOffset -> Int -> TwoDiskProg BS.ByteString
readBytes off len =
  if not (off `mod` blocksize == 0 && len `mod` blocksize == 0) then
    error $ "misaligned read at " ++ show off ++ " length " ++ show len
  else ArrayAPI.read (_RD__rd _TD__td)
       (fromIntegral off `div` blocksize)
       (fromIntegral len `div` blocksize)

-- |wrapper for Array write that checks for invalid parameters and converts types
writeBytes :: ByteOffset -> BS.ByteString -> TwoDiskProg ()
writeBytes off dat =
  if not (off `mod` blocksize == 0 && BS.length dat `mod` blocksize == 0) then
    error $ "misaligned write at " ++ show off ++ " length " ++ show (BS.length dat)
  else ArrayAPI.write (_RD__rd _TD__td)
       (fromIntegral off `div` blocksize)
       (fromIntegral $ BS.length dat `div` blocksize)
       dat

-- |wrapper for replicated disk recovery procedure
recover :: TwoDiskProg ()
recover = ArrayAPI.recover (_RD__rd _TD__td)
