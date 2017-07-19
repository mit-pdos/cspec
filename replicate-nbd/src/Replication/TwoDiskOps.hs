{-# LANGUAGE PackageImports #-}
module Replication.TwoDiskOps where

import                   Control.Monad (void)
import                   Control.Monad.Reader (reader, liftIO)
import qualified         Data.ByteString as BS
import                   Replication.TwoDiskEnvironment
import                   Sectors
import                   System.IO (SeekMode(..))
import "unix-bytestring" System.Posix.IO.ByteString
import                   System.Posix.Types (Fd)
import                   System.Posix.Unistd (fileSynchronise)
import                   TwoDiskAPI
import                   Utils.Conversion

getDisk :: Coq_diskId -> TheProg (Maybe Fd)
getDisk Coq_d0 = reader disk0 >>= liftIO
getDisk Coq_d1 = reader disk1 >>= liftIO

ifExists :: Coq_diskId -> (Fd -> IO a) -> TheProg (DiskResult a)
ifExists d m = do
  mfd <- getDisk d
  liftIO $ case mfd of
      Just fd -> Working <$> m fd
      Nothing -> return Failed

read :: Coq_diskId -> Coq_addr -> TheProg (DiskResult BS.ByteString)
read d a = ifExists d $ \fd ->
  fdPread fd blocksize (fromIntegral $ addrToOffset a)

write :: Coq_diskId -> Coq_addr -> BS.ByteString -> TheProg (DiskResult ())
write d a b = ifExists d $ \fd ->
  void $ fdPwrite fd b (fromIntegral $ addrToOffset a)

sync :: Coq_diskId -> TheProg (DiskResult ())
sync d = ifExists d $ \fd ->
  void $ fileSynchronise fd

-- |implementation of two disk DiskSize operation - note that this size is
-- reported to Coq in blocks
diskSize :: Coq_diskId -> TheProg (DiskResult Integer)
diskSize d = ifExists d $ \fd -> do
    off <- fdSeek fd SeekFromEnd 0
    return (fromIntegral off `div` blocksize)
