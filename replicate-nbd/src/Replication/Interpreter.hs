{-# LANGUAGE Rank2Types #-}
module Replication.Interpreter where

import qualified Data.ByteString as BS
import           Prog
import           System.Directory (doesFileExist)
import           System.IO
import           TwoDiskProg
import           Unsafe.Coerce
import           Utils.Conversion

type Interpreter = forall t. TD__Coq_prog t -> IO t

data Config =
  Config { disk0Path :: FilePath
         , disk1Path :: FilePath }

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

interpreter :: Config -> Interpreter
interpreter c = interp
  where
    getDisk :: Coq_diskId -> FilePath
    getDisk Coq_d0 = disk0Path c
    getDisk Coq_d1 = disk1Path c

    ifExists :: FilePath -> IO a -> IO (DiskResult a)
    ifExists path a = do
      exists <- doesFileExist path
      if exists then Working `fmap` a
        else return Failed

    interp :: Interpreter
    interp (Prim op) = case op of
      -- TODO: catch exceptions and return Failed
      TD__Read d a ->
        let path = getDisk d in
        unsafeCoerce <$> ifExists path $
          withBinaryFile path ReadMode $ \h ->
            pread h blocksize (addrToOffset a)
      TD__Write d a b ->
        let path = getDisk d in
        unsafeCoerce <$> ifExists path $
            withBinaryFile path ReadWriteMode $ \h ->
              pwrite h b (addrToOffset a)
      TD__DiskSize d ->
        let path = getDisk d in
        unsafeCoerce <$> ifExists path $
          withBinaryFile path ReadMode $ \h -> do
            sz <- hFileSize h
            return (sz `div` blocksize::Integer)
    interp (Ret t) = return t
    interp (Bind p1 p2) = do
      r <- interp p1
      interp (p2 r)
