{-# LANGUAGE Rank2Types #-}
module Replication.DiskOps where

import           Control.Monad (unless)
import           Control.Monad.Reader (ReaderT)
import qualified Data.ByteString as BS
import           ReplicatedDisk
import           Replication.TwoDiskEnvironment
import           SeqDiskAPI
import           TwoDiskImpl (_TD__td)
import           Utils.Conversion

-- TODO: use newtype for block things

type BlockOffset = Int
type ByteOffset = Int

rdRead :: BlockOffset -> ReaderT Config IO BS.ByteString
rdRead off = _RD__prim _TD__td $ D__Read (fromIntegral off)

rdWrite :: BlockOffset -> BS.ByteString -> ReaderT Config IO ()
rdWrite off dat = unit <$> _RD__prim _TD__td (D__Write (fromIntegral off) dat)

readBytes :: ByteOffset -> Int -> ReaderT Config IO BS.ByteString
readBytes off len =
  if not (off `mod` blocksize == 0 && len `mod` blocksize == 0) then
    error $ "misaligned read at " ++ show off ++ " length " ++ show len
  else loop (off `div` blocksize) (len `div` blocksize)
  where loop _ 0 = return BS.empty
        loop blockOff l = do
          b <- rdRead blockOff
          s' <- loop (blockOff+1) (l-1)
          return (BS.append b s')

writeBytes :: ByteOffset -> BS.ByteString -> ReaderT Config IO ()
writeBytes off dat =
  if not (off `mod` blocksize == 0 && BS.length dat `mod` blocksize == 0) then
    error $ "misaligned write at " ++ show off ++ " length " ++ show (BS.length dat)
  else loop (off `div` blocksize) dat
  where loop blockOff s = unless (BS.length s == 0) $ do
          rdWrite blockOff (BS.take blocksize s)
          loop (blockOff+1) (BS.drop blocksize s)

recover :: ReaderT Config IO ()
recover = unit <$> _RD__recover _TD__td
