{-# LANGUAGE PackageImports #-}
module BadSectorDisk.Ops where

import                   Control.Monad (void)
import                   Control.Monad.Reader (reader, liftIO)
import qualified         Data.ByteString as BS
import qualified         Data.Char
import                   BadSectorDisk.Env
import                   Sectors
import                   System.IO (SeekMode(..))
import "unix-bytestring" System.Posix.IO.ByteString
import                   System.Posix.Types (Fd)
import                   System.Posix.Unistd (fileSynchronise)
import                   Utils.Conversion

read :: Coq_addr -> TheProc BS.ByteString
read a = do
  fd <- reader diskHandle
  bs <- reader badSector
  if a == bs then
    return $ BS.replicate blocksize $ fromIntegral $ Data.Char.ord 'A'
  else
    liftIO $ fdPread fd blocksize (fromIntegral $ addrToOffset a)

write :: Coq_addr -> BS.ByteString -> TheProc ()
write a b = do
  fd <- reader diskHandle
  liftIO $ fdPwrite fd b (fromIntegral $ addrToOffset a)
  return ()

-- |implementation of two disk DiskSize operation - note that this size is
-- reported to Coq in blocks
size :: TheProc Integer
size = do
  fd <- reader diskHandle
  off <- liftIO $ fdSeek fd SeekFromEnd 0
  return (fromIntegral off `div` blocksize)

getBadSector :: TheProc Integer
getBadSector = do
  bs <- reader badSector
  return bs
