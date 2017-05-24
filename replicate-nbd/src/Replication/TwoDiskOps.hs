{-# LANGUAGE Rank2Types #-}
module Replication.TwoDiskOps where

import           Control.Monad.Reader (reader, liftIO)
import qualified Data.ByteString as BS
import           Disk
import           Replication.TwoDiskEnvironment
import           System.Directory (doesFileExist)
import           System.IO
import           TwoDiskAPI
import           Utils.Conversion

pread :: Handle -> Int -> FileOffset -> IO BS.ByteString
pread h len off = do
  hSeek h AbsoluteSeek off
  BS.hGet h len

pwrite :: Handle -> BS.ByteString -> FileOffset -> IO ()
pwrite h dat off = do
  hSeek h AbsoluteSeek off
  BS.hPut h dat

getDisk :: Coq_diskId -> Env -> FilePath
getDisk Coq_d0 = disk0Path
getDisk Coq_d1 = disk1Path

ifExists :: FilePath -> IO a -> IO (DiskResult a)
ifExists path a = do
  exists <- doesFileExist path
  if exists then Working <$> a
    else return Failed

read :: Coq_diskId -> Coq_addr -> TwoDiskProg (DiskResult BS.ByteString)
read d a = do
 path <- reader $ getDisk d
 liftIO . ifExists path $
   withBinaryFile path ReadMode $ \h ->
   pread h blocksize (addrToOffset a)

write :: Coq_diskId -> Coq_addr -> BS.ByteString -> TwoDiskProg (DiskResult ())
write d a b = do
  path <- reader $ getDisk d
  liftIO . ifExists path $
    withBinaryFile path ReadWriteMode $ \h ->
    pwrite h b (addrToOffset a)

diskSize :: Coq_diskId -> TwoDiskProg (DiskResult Integer)
diskSize d = do
  path <- reader $ getDisk d
  liftIO . ifExists path $
    withBinaryFile path ReadMode $ \h -> do
      sz <- hFileSize h
      return (sz `div` blocksize::Integer)
