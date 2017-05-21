{-# LANGUAGE OverloadedStrings, Rank2Types  #-}

module Network.NBD where

import           Conduit
import           Control.Exception.Base (Exception)
import           Control.Monad (when)
import           Control.Monad.Reader (runReaderT)
import           Data.Bits
import qualified Data.ByteString as BS
import           Data.Conduit.Cereal
import           Data.Conduit.Network
import           Data.Serialize
import           Network.NBD.Data
import qualified Replication.DiskOps as RD
import           Replication.Interpreter
import           Replication.TwoDiskEnvironment

-- IANA reserved port 10809
--
-- high-level overview of protocol:
-- on connection:
-- negotiate
--   S: INIT_PASSWD, NEW_MAGIC, NBD_FLAG_FIXED_NEWSTYLE
--   C: flags, should have NBD_FLAG_C_FIXED_NEWSTYLE
--   loop (options)
--     C: NEW_MAGIC, type, length, data (length bytes)
--     until type == NBD_OPT_EXPORT_NAME
--   S: export size, NBD_FLAG_HAS_FLAGS (| read-only | flush), 124 zeroes
-- transmission
--   loop (commands)
--     C: NBD_REQUEST_MAGIC, flags (fua), type, handle, offset, length
--     (for write) C: data (length bytes)
--     S: NBD_REPLY_MAGIC, error, (same) handle
--     (for read) S: data (length bytes)
--
-- see https://sourceforge.net/p/nbd/code/ci/master/tree/doc/proto.md for a
-- detailed protocol description

data ServerOptions = ServerOptions
  { diskPaths :: (FilePath, FilePath)
  , logCommands :: Bool }

type ByteConduit m r = ConduitM BS.ByteString BS.ByteString m r

type ExportName = BS.ByteString

-- get an option, or return an export name
getOption :: MonadThrow m => ByteConduit m (Either ExportName NbdOption)
getOption = do
  magic <- sinkGet getWord64be
  when (magic /= nbd_C_OPT_MAGIC) $
    throwM $ InvalidMagic "client option" magic
  sinkGet $ do
    opt <- toEnum . fromIntegral <$> getWord32be
    len <- fromIntegral <$> getWord32be
    case opt of
      ExportName -> Left <$> getBytes len
      _ -> getBytes len >> return (Right opt)

negotiateNewstyle :: MonadThrow m => ByteConduit m ExportName
negotiateNewstyle = do
  yield newstylePrelude
  clientFlags <- sinkGet getWord32be
  when (clientFlags .&. nbd_FLAG_C_FIXED_NEWSTYLE == 0) $
    throwM $ InvalidClientFlags clientFlags
  handleOptions
  where
    newstylePrelude :: BS.ByteString
    newstylePrelude = runPut $ do
      putWord64be nbd_INIT_PASSWD
      putWord64be nbd_NEW_MAGIC
      putWord16be (0 .|. nbd_FLAG_FIXED_NEWSTYLE)

    handleOptions = do
      opt <- getOption
      case opt of
        Left n -> return n
        Right _ ->
          -- we actually ignore all options
          handleOptions


sendExportInformation :: Monad m => ByteCount -> ByteConduit m ()
sendExportInformation len = sourcePut $ do
    putWord64be $ fromIntegral len
    putWord16be flags
    putByteString zeroes
  where
    zeroes = BS.replicate 124 0
    flags = nbd_FLAG_HAS_FLAGS

getCommand :: (MonadThrow m, MonadIO m) => ByteConduit m Command
getCommand = do
  magic <- sinkGet getWord32be
  when (magic /= nbd_REQUEST_MAGIC) $
    throwM $ InvalidMagic "request" (fromIntegral magic)
  (_, typ, handle, offset, len) <- sinkGet $ label "request header" $ (,,,,) <$>
    getWord16be <*> -- flags (ignored)
    getWord16be <*> -- type
    getWord64be <*> -- handle
    (fromIntegral <$> getWord64be) <*> -- offset
    (fromIntegral <$> getWord32be) -- length
  case typ of
    0 -> return $ Read handle offset len
    1 -> do
      dat <- sinkGet $ getBytes len
      return $ Write handle offset dat
    2 -> return Disconnect
    _ -> return $ UnknownCommand typ handle offset len

sendReply :: Monad m => Handle -> ErrorCode -> ByteConduit m ()
sendReply h err = sourcePut $ do
  putWord32be nbd_REPLY_MAGIC
  putWord32be (errCode err)
  putWord64be h

withConfig :: Config -> ReaderT Config IO a -> IO a
withConfig c m = runReaderT m c

handleCommands :: (MonadThrow m, MonadIO m) => Bool -> Config -> ByteConduit m ()
handleCommands doLog c = handle
  where
    debug = liftIO . when doLog . putStrLn
    handle = do
      cmd <- getCommand
      case cmd of
        -- TODO: insert bounds checks
        Read h off len -> do
          debug $ "read at " ++ show off ++ " len " ++ show len
          bs <- liftIO . withConfig c $ RD.readBytes off len
          sendReply h NoError
          sourcePut $ putByteString bs
          handle
        Write h off dat -> do
          debug $ "write at " ++ show off ++ " len " ++ show (BS.length dat)
          liftIO . withConfig c $ RD.writeBytes off dat
          sendReply h NoError
          handle
        Disconnect -> do
          debug "disconnect command"
          return ()
        UnknownCommand _ h _ _ -> do
          debug $ "unknown command " ++ show cmd
          sendReply h EInval
          handle

data SizeMismatchException =
  SizeMismatchException { size0 :: Integer
                        , size1 :: Integer  }
  deriving (Eq, Show)

instance Exception SizeMismatchException

runServer :: ServerOptions -> IO ()
runServer ServerOptions {diskPaths=(fn0, fn1), logCommands=doLog} =
  let c = Config fn0 fn1 in do
  putStrLn "recovering..."
  withConfig c RD.recover
  putStrLn "serving on localhost:10809"
  let settings = serverSettings 10809 "127.0.0.1" in
    runTCPServer settings $ \ad -> do
      runConduit $ appSource ad .| do
        liftIO $ putStrLn "received connection"
        name <- negotiateNewstyle
        liftIO $ when (name /= "") $
          putStrLn $ "ignoring non-default export name " ++ show name
        msz <- liftIO $ diskSizes c
        case msz of
          Left (sz0, sz1) -> throwM $ SizeMismatchException sz0 sz1
          Right sz -> sendExportInformation (fromIntegral sz)
        liftIO $ putStrLn "finished negotiation"
        handleCommands doLog c
        .| appSink ad
      putStrLn "client disconnect"
