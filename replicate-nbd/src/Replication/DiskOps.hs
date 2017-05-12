{-# LANGUAGE Rank2Types #-}
module Replication.DiskOps where

import           Control.Monad (unless)
import qualified Data.ByteString as BS
import           Interpreter.TwoDisk
import           ReplicatedDisk
import           Utils.Conversion

-- TODO: use newtype for block things

type BlockOffset = Int
type ByteOffset = Int

rdRead :: Interpreter -> BlockOffset -> IO BS.ByteString
rdRead run off = run $ _RD__coq_Read (numToNat off)

rdWrite :: Interpreter -> BlockOffset -> BS.ByteString -> IO ()
rdWrite run off dat = fmap unit . run $ _RD__coq_Write (numToNat off) dat

readBytes :: Interpreter -> ByteOffset -> Int -> IO BS.ByteString
readBytes run off len =
  if not (off `mod` 4096 == 0 && len `mod` 4096 == 0) then
    error $ "misaligned read at " ++ show off ++ " length " ++ show len
  else loop (off `div` 4096) (len `div` 4096)
  where loop _ 0 = return BS.empty
        loop blockOff l = do
          b <- rdRead run blockOff
          s' <- loop (blockOff+1) (l-1)
          return (BS.append b s')

writeBytes :: Interpreter -> ByteOffset -> BS.ByteString -> IO ()
writeBytes run off dat =
  if not (off `mod` 4096 == 0 && BS.length dat `mod` 4096 == 0) then
    error $ "misaligned write at " ++ show off ++ " length " ++ show (BS.length dat)
  else loop (off `div` 4096) dat
  where loop blockOff s = unless (BS.length s == 0) $ do
          rdWrite run blockOff (BS.take 4096 s)
          loop (blockOff+1) (BS.drop 4096 s)
