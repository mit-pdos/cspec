{-# LANGUAGE PackageImports #-}
module Replication.TwoDiskOps where

import                   Control.Monad (void)
import                   Control.Monad.Reader (reader, liftIO)
import qualified         Data.ByteString as BS
import                   Disk
import                   Replication.TwoDiskEnvironment
import                   System.Directory (doesFileExist)
import                   System.IO (SeekMode(..))
import                   System.Posix.IO (closeFd)
import "unix-bytestring" System.Posix.IO.ByteString
import                   System.Posix.Types (Fd)
import                   TwoDiskAPI
import                   Utils.Conversion

getDisk :: Coq_diskId -> Env -> (FilePath, Fd)
getDisk Coq_d0 = disk0
getDisk Coq_d1 = disk1

ifExists :: Coq_diskId -> (Fd -> IO a) -> TwoDiskProg (DiskResult a)
ifExists d m = do
  (path, fd) <- reader $ getDisk d
  liftIO $ do
    exists <- doesFileExist path
    if exists
      then Working <$> m fd
      else closeFd fd >> return Failed

read :: Coq_diskId -> Coq_addr -> TwoDiskProg (DiskResult BS.ByteString)
read d a = ifExists d $ \fd ->
  fdPread fd blocksize (fromIntegral $ addrToOffset a)

write :: Coq_diskId -> Coq_addr -> BS.ByteString -> TwoDiskProg (DiskResult ())
write d a b = ifExists d $ \fd ->
  void $ fdPwrite fd b (fromIntegral $ addrToOffset a)

-- |implementation of two disk DiskSize operation - note that this size is
-- reported to Coq in blocks
diskSize :: Coq_diskId -> TwoDiskProg (DiskResult Integer)
diskSize d = ifExists d $ \fd -> do
    off <- fdSeek fd SeekFromEnd 0
    return (fromIntegral off `div` blocksize)
