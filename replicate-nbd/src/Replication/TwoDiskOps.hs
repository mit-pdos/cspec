{-# LANGUAGE PackageImports #-}
module Replication.TwoDiskOps where

import                   Control.Monad.Reader (reader, liftIO)
import qualified         Data.ByteString as BS
import                   Disk
import                   Replication.TwoDiskEnvironment
import                   System.Directory (doesFileExist)
import                   System.IO
import "unix-bytestring" System.Posix.IO.ByteString
import                   System.Posix.Types (Fd)
import                   TwoDiskAPI
import                   Utils.Conversion

pread :: Handle -> Int -> FileOffset -> IO BS.ByteString
pread h len off = do
  hSeek h AbsoluteSeek off
  BS.hGet h len

pwrite :: Handle -> BS.ByteString -> FileOffset -> IO ()
pwrite h dat off = do
  hSeek h AbsoluteSeek off
  BS.hPut h dat

getDisk :: Coq_diskId -> Env -> Fd
getDisk Coq_d0 = disk0Fd
getDisk Coq_d1 = disk1Fd

ifExists :: FilePath -> IO a -> IO (DiskResult a)
ifExists path a = do
  exists <- doesFileExist path
  if exists then Working <$> a
    else return Failed

read :: Coq_diskId -> Coq_addr -> TwoDiskProg (DiskResult BS.ByteString)
read d a = do
 fd <- reader $ getDisk d
 liftIO $ Working <$> fdPread fd blocksize (fromIntegral $ addrToOffset a)

write :: Coq_diskId -> Coq_addr -> BS.ByteString -> TwoDiskProg (DiskResult ())
write d a b = do
  fd <- reader $ getDisk d
  liftIO $ fdPwrite fd b (fromIntegral $ addrToOffset a) >> return (Working ())

diskSize :: Coq_diskId -> TwoDiskProg (DiskResult Integer)
diskSize d = do
  fd <- reader $ getDisk d
  liftIO $ Working <$> do
    off <- fdSeek fd SeekFromEnd 0
    return (fromIntegral off `div` blocksize::Integer)
