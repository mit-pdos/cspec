module Support
  (
    encode_tid_fn
  , decode_tid_fn
  , POP3Conn(..)
  , SMTPConn(..)
  ) where

import Data.List
import Data.IORef
import System.IO
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC8

parse_number :: BS.ByteString -> Integer
parse_number = read . BSC8.unpack

encode_tid_fn :: Integer -> Integer -> BS.ByteString
encode_tid_fn tid fn = BS.concat [BSC8.pack (show tid), ".", BSC8.pack (show fn)]

decode_tid_fn :: BS.ByteString -> (Integer, Integer)
decode_tid_fn fn =
  case BSC8.findIndex (=='.') fn of
    Nothing -> (0, 0)
    Just i -> let (tidstr, fnstr) = BS.splitAt i fn in
      (parse_number tidstr, parse_number (BS.tail fnstr))

data POP3Conn =
  POP3Conn Handle

data SMTPConn =
  SMTPConn Handle
