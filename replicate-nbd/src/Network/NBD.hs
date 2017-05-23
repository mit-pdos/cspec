{-# LANGUAGE OverloadedStrings, Rank2Types  #-}

module Network.NBD where

import           Conduit
import           Control.Concurrent (forkIO)
import           Control.Concurrent.MVar (newEmptyMVar, putMVar, takeMVar)
import           Control.Exception.Base (Exception)
import           Control.Monad (when)
import           Data.Bits
import qualified Data.ByteString as BS
import           Data.Conduit.Cereal
import           Data.Conduit.Network
import           Data.Serialize
import           Interface (InitResult(..))
import qualified NbdData as Nbd
import           Network.NBD.Data
import           Replication.TwoDiskEnvironment
import           Replication.TwoDiskOps
import qualified Server
import           System.Exit (die)
import           Utils.Conversion

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

-- negotiate a set of options with the client
-- options are currently all ignored, so that this process simply returns the
-- export name requested by the client
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

-- start transmission after negotiation by informing the client about the export
sendExportInformation :: Monad m => ByteCount -> ByteConduit m ()
sendExportInformation len = sourcePut $ do
    putWord64be $ fromIntegral len
    putWord16be flags
    putByteString zeroes
  where
    zeroes = BS.replicate 124 0
    flags = nbd_FLAG_HAS_FLAGS

-- parse a command from the client during the transmission phase
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

-- send an error code reply to the client (data is sent separately afterward,
-- for reads)
sendReply :: Monad m => Handle -> ErrorCode -> ByteConduit m ()
sendReply h err = sourcePut $ do
  putWord32be nbd_REPLY_MAGIC
  putWord32be (errCode err)
  putWord64be h

-- TODO: get rid of Command, replace with Nbd.Request
commandToRequest :: Command -> Nbd.Request
commandToRequest c = case c of
  Read h off len -> Nbd.Read h (fromIntegral off `div` blocksize) (fromIntegral len `div` blocksize)
  Write h off dat -> Nbd.Write h (fromIntegral off `div` blocksize) (fromIntegral (BS.length dat `div` blocksize)) dat
  Disconnect -> Nbd.Disconnect
  UnknownCommand _ h _ _ -> Nbd.UnknownOp h

-- TODO: get rid of ErrorCode in Haskell, replace with Nbd.ErrorCode
nbdErrCodeToErrCode :: Nbd.ErrorCode -> ErrorCode
nbdErrCodeToErrCode e = case e of
  Nbd.ESuccess -> NoError
  Nbd.EInvalid -> EInval

sendResponse :: MonadIO m => Nbd.Response -> ByteConduit m ()
sendResponse (Nbd.Build_Response h e _ dat) = do
  sendReply h (nbdErrCodeToErrCode e)
  sourcePut $ putByteString dat

handleCommands :: (MonadThrow m, MonadIO m) => Bool -> Env -> ByteConduit m ()
handleCommands doLog e = handle
  where
    debug :: (MonadThrow m, MonadIO m) => String -> ByteConduit m ()
    debug = liftIO . when doLog . putStrLn
    handle = do
      cmd <- getCommand
      case cmd of
        Read _ off len -> debug $ "read at " ++ show off ++ " of length " ++ show len
        Write _ off dat -> debug $ "write at " ++ show off ++ " of length " ++ show (BS.length dat)
        Disconnect -> debug "disconnect command"
        UnknownCommand i _ _ _ -> debug $ "unknown command with id " ++ show i
      r <- liftIO $ do
        putMVar (requests e) (commandToRequest cmd)
        takeMVar (responses e)
      sendResponse r
      handle

data SizeMismatchException =
  SizeMismatchException { size0 :: Integer
                        , size1 :: Integer  }
  deriving (Eq, Show)

instance Exception SizeMismatchException

runServer :: ServerOptions -> IO ()
runServer ServerOptions
  { diskPaths=(fn0, fn1),
    logCommands=doLog} = do
  e <- Env fn0 fn1 <$> newEmptyMVar <*> newEmptyMVar
  putStrLn "serving on localhost:10809"
  _ <- liftIO . forkIO $ runTD e Server.serverLoop
  let settings = serverSettings 10809 "127.0.0.1" in
    runTCPServer settings $ \ad ->
    -- these are all the steps of a single client connection
      let nbdConnection = do
            liftIO $ putStrLn "received connection"
          -- negotiate
            name <- negotiateNewstyle
            liftIO $ when (name /= "") $
              putStrLn $ "ignoring non-default export name " ++ show name
            msz <- liftIO . runTD e $ diskSizes
            case msz of
              Left (sz0, sz1) -> throwM $ SizeMismatchException sz0 sz1
              Right sz ->
                -- start transmission phase
                sendExportInformation (fromIntegral sz)
            liftIO $ putStrLn "finished negotiation"
            handleCommands doLog e
          -- handle commands in a loop, which terminates upon receiving the
          -- Disconnect command
            liftIO $ putStrLn "client disconnect" in
      -- assemble a conduit using the TCP server as input and output
      runConduit $ appSource ad .| nbdConnection .| appSink ad

initServer :: (FilePath, FilePath) -> IO ()
initServer (fn0, fn1) = do
  e <- Env fn0 fn1 <$> newEmptyMVar <*> newEmptyMVar
  r <- runTD e Server.init
  case r of
    Initialized -> return ()
    InitFailed -> die "initialization failed! are disks of different sizes?"
