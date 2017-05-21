{-# LANGUAGE Rank2Types #-}
module Replication.Interpreter where

import           Control.Monad.Reader (ReaderT, reader, liftIO)
import qualified Data.ByteString as BS
import           Disk
import           Replication.TwoDiskEnvironment
import           System.Directory (doesFileExist)
import           System.IO
import           TwoDiskAPI
import           Utils.Conversion

-- this operation is unfortunate: we use it to check the invariant that the
-- disks are the same size for safety, but it would be nice to get it from Coq
-- somehow
diskSizes :: Config -> IO (Either (Integer, Integer) Integer)
diskSizes c = do
  msz0 <- maybeSize (disk0Path c)
  msz1 <- maybeSize (disk1Path c)
  return $ case (msz0, msz1) of
    (Just sz0, Just sz1) -> if sz0 == sz1 then Right sz0 else Left (sz0, sz1)
    (Just sz, Nothing) -> Right sz
    (Nothing, Just sz) -> Right sz
    (Nothing, Nothing) -> Right 0
  where
    maybeSize path = do
      exists <- doesFileExist path
      if not exists then return Nothing
        else withBinaryFile (disk1Path c) ReadMode $ \h ->
          Just <$> hFileSize h

pread :: Handle -> Int -> FileOffset -> IO BS.ByteString
pread h len off = do
  hSeek h AbsoluteSeek off
  BS.hGet h len

pwrite :: Handle -> BS.ByteString -> FileOffset -> IO ()
pwrite h dat off = do
  hSeek h AbsoluteSeek off
  BS.hPut h dat

getDisk :: Coq_diskId -> Config -> FilePath
getDisk Coq_d0 = disk0Path
getDisk Coq_d1 = disk1Path

ifExists :: FilePath -> IO a -> IO (DiskResult a)
ifExists path a = do
  exists <- doesFileExist path
  if exists then Working <$> a
    else return Failed

tdRead :: Coq_diskId -> Coq_addr
       -> ReaderT Config IO (DiskResult BS.ByteString)
tdRead d a = do
  path <- reader $ getDisk d
  liftIO . ifExists path $
    withBinaryFile path ReadMode $ \h ->
      pread h blocksize (addrToOffset a)

tdWrite :: Coq_diskId -> Coq_addr -> BS.ByteString
        -> ReaderT Config IO (DiskResult ())
tdWrite d a b = do
  path <- reader $ getDisk d
  liftIO . ifExists path $
      withBinaryFile path ReadWriteMode $ \h ->
        pwrite h b (addrToOffset a)

tdDiskSize :: Coq_diskId
           -> ReaderT Config IO (DiskResult Integer)
tdDiskSize d = do
  path <- reader $ getDisk d
  liftIO . ifExists path $
    withBinaryFile path ReadMode $ \h -> do
      sz <- hFileSize h
      return (sz `div` blocksize::Integer)
