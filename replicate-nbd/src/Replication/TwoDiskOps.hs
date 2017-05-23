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

-- this operation is unfortunate: we use it to check the invariant that the
-- disks are the same size for safety, but it would be nice to get it from Coq
-- somehow
diskSizes :: TwoDiskProg (Either (Integer, Integer) Integer)
diskSizes = do
  msz0 <- maybeSize =<< reader disk0Path
  msz1 <- maybeSize =<< reader disk1Path
  return $ case (msz0, msz1) of
    (Just sz0, Just sz1) -> if sz0 == sz1 then Right sz0 else Left (sz0, sz1)
    (Just sz, Nothing) -> Right sz
    (Nothing, Just sz) -> Right sz
    (Nothing, Nothing) -> Right 0
  where
    maybeSize :: FilePath -> TwoDiskProg (Maybe Integer)
    maybeSize path = liftIO $ do
      exists <- doesFileExist path
      if not exists then return Nothing
        else withBinaryFile path ReadMode $ \h ->
          Just <$> hFileSize h

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
