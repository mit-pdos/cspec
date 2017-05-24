{-# LANGUAGE DeriveDataTypeable #-}
module Network.NBD.Data where

import           Control.Exception.Base (Exception)
import           Data.Bits
import qualified Data.ByteString as BS
import           Data.Typeable (Typeable)
import           GHC.Word
import           NbdData

{-# ANN module ("HLint: ignore Use camelCase"::String) #-}

-- Represent NBD data and constants

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

-- if we supported other flags (including read-only, flush), then we would want
-- to have an enum(set) for export flags
nbd_FLAG_HAS_FLAGS :: Bits a => a
nbd_FLAG_HAS_FLAGS = bit 0

-- Handle is a Word64, defined by extraction
type ByteCount = Int
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

nbd_REPLY_MAGIC :: Word32
nbd_REPLY_MAGIC = 0x67446698

errCode :: ErrorCode -> Word32
errCode err = case err of
  ESuccess -> 0
  EInvalid -> 22
  ENospc -> 28
