{-# LANGUAGE Rank2Types #-}
module Replication.DiskOps where

import           Control.Monad (unless)
import qualified Data.ByteString as BS
import           Replication.Interpreter
import           ReplicatedDisk
import           Utils.Conversion

-- TODO: use newtype for block things

type BlockOffset = Int
type ByteOffset = Int

rdRead :: Interpreter -> BlockOffset -> IO BS.ByteString
rdRead run off = run $ _RD__coq_Read (fromIntegral off)

rdWrite :: Interpreter -> BlockOffset -> BS.ByteString -> IO ()
rdWrite run off dat = fmap unit . run $ _RD__coq_Write (fromIntegral off) dat

readBytes :: Interpreter -> ByteOffset -> Int -> IO BS.ByteString
readBytes run off len =
  if not (off `mod` blocksize == 0 && len `mod` blocksize == 0) then
    error $ "misaligned read at " ++ show off ++ " length " ++ show len
  else loop (off `div` blocksize) (len `div` blocksize)
  where loop _ 0 = return BS.empty
        loop blockOff l = do
          b <- rdRead run blockOff
          s' <- loop (blockOff+1) (l-1)
          return (BS.append b s')

writeBytes :: Interpreter -> ByteOffset -> BS.ByteString -> IO ()
writeBytes run off dat =
  if not (off `mod` blocksize == 0 && BS.length dat `mod` blocksize == 0) then
    error $ "misaligned write at " ++ show off ++ " length " ++ show (BS.length dat)
  else loop (off `div` blocksize) dat
  where loop blockOff s = unless (BS.length s == 0) $ do
          rdWrite run blockOff (BS.take blocksize s)
          loop (blockOff+1) (BS.drop blocksize s)

recover :: Interpreter -> IO ()
recover run = fmap unit . run $ _RD__coq_Recover
