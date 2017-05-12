{-# LANGUAGE OverloadedStrings, Rank2Types  #-}
{-# LANGUAGE DeriveDataTypeable #-}

module Network.NBD where

import           Conduit
import           Control.Exception.Base (Exception)
import           Control.Monad (when)
import           Data.Bits
import qualified Data.ByteString as BS
import           Data.Conduit.Cereal
import           Data.Conduit.Network
import           Data.Serialize
import           Data.Text (Text)
import           Data.Text.Encoding (decodeUtf8)
import           Data.Typeable (Typeable)
import           GHC.Word

-- amazingly enough, the expression inside this annotation is of ambiguous type
-- due to OverloadedStrings
{-# ANN module ("HLint: ignore Use camelCase"::String) #-}

nbd_INIT_PASSWD :: Word64
nbd_INIT_PASSWD = 0x4e42444d41474943

nbd_NEW_MAGIC :: Word64
nbd_NEW_MAGIC = 0x49484156454F5054

nbd_FLAG_FIXED_NEWSTYLE :: Bits a => a
nbd_FLAG_FIXED_NEWSTYLE = bit 0

nbd_FLAG_C_FIXED_NEWSTYLE :: Bits a => a
nbd_FLAG_C_FIXED_NEWSTYLE = bit 0

data ProtocolException =
  InvalidClientFlags !Word32
  | InvalidMagic String !Word64
  deriving (Show, Typeable)

instance Exception ProtocolException

-- IANA reserved port 10809
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

data NbdOption = ExportName
               | Abort
               | ListExports
               | UnknownOption
  deriving (Show, Eq)

instance Enum NbdOption where
  toEnum n = case n of
    1 -> ExportName
    2 -> Abort
    3 -> ListExports
    _ -> UnknownOption

  fromEnum a = case a of
    ExportName -> 1
    Abort -> 2
    ListExports -> 3
    UnknownOption -> 4

nbd_C_OPT_MAGIC :: Word64
nbd_C_OPT_MAGIC = 0x49484156454F5054 -- same as nbd_NEW_MAGIC

type ByteConduit m r = ConduitM BS.ByteString BS.ByteString m r

type ExportName = Text

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
      ExportName -> Left . decodeUtf8 <$> getBytes len
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

type ByteCount = Int

-- if we supported other flags (including read-only, flush), then we would want
-- to have an enum(set) for export flags
nbd_FLAG_HAS_FLAGS :: Bits a => a
nbd_FLAG_HAS_FLAGS = bit 0

sendExportInformation :: Monad m => ByteCount -> ByteConduit m ()
sendExportInformation len = sourcePut $ do
    putWord64be $ fromIntegral len
    putWord16be flags
    putByteString zeroes
  where
    zeroes = BS.replicate 124 0
    flags = nbd_FLAG_HAS_FLAGS

type Handle = Word64
type FileOffset = Int

data Command = Read { readHandle :: !Handle
                    , readFrom :: !FileOffset
                    , readLength :: !ByteCount }
             | Write { writeHandle :: !Handle
                     , writeFrom :: !FileOffset
                     , writeData :: !BS.ByteString }
             | Disconnect
             | UnknownCommand { unknownCommandId :: !Word16
                              , unknownCommandHandle :: !Handle
                              , unknownCommandOffset :: !FileOffset
                              , unknownCommandLength :: !ByteCount }
  deriving (Show, Eq)

nbd_REQUEST_MAGIC :: Word32
nbd_REQUEST_MAGIC = 0x25609513

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

nbd_REPLY_MAGIC :: Word32
nbd_REPLY_MAGIC = 0x67446698

data ErrorCode = NoError
               | EInval
               | ENospc

errCode :: ErrorCode -> Word32
errCode err = case err of
  NoError -> 0
  EInval -> 22
  ENospc -> 28

sendReply :: Monad m => Handle -> ErrorCode -> ByteConduit m ()
sendReply h err = sourcePut $ do
  putWord32be nbd_REPLY_MAGIC
  putWord32be (errCode err)
  putWord64be h

handleCommands :: (MonadThrow m, MonadIO m) => ByteConduit m ()
handleCommands = do
  cmd <- getCommand
  case cmd of
    -- TODO: insert bounds checks
    Read h off len -> do
      liftIO $ putStrLn $ "fake read from " ++ show off ++
        " length " ++ show len
      sendReply h NoError
      sourcePut $ putByteString (BS.replicate len 0)
      handleCommands
    Write h off dat -> do
      liftIO $ putStrLn $ "fake write to " ++ show off ++
        " length " ++ show (BS.length dat)
      sendReply h NoError
      handleCommands
    Disconnect -> do
      liftIO $ putStrLn "disconnect command"
      return ()
    UnknownCommand _ h _ _ -> do
      liftIO $ putStrLn $ "unknown command " ++ show cmd
      sendReply h EInval
      handleCommands

runServer :: IO ()
runServer =
  let settings = serverSettings 10809 "127.0.0.1" in
  runTCPServer settings $ \ad -> do
    runConduit $ appSource ad .| do
      liftIO $ putStrLn "received connection"
      name <- negotiateNewstyle
      liftIO $ when (name /= "") $
        putStrLn $ "ignoring non-default export name " ++ show name
      sendExportInformation (1024*1024)
      liftIO $ putStrLn "finished negotiation"
      handleCommands
      .| appSink ad
    putStrLn "client disconnect"
