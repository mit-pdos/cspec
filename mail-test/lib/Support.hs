module Support where

import Data.List
import Data.IORef
import System.IO

encode_tid_fn :: Integer -> Integer -> String
encode_tid_fn tid fn = (show tid) ++ "." ++ (show fn)

decode_tid_fn :: String -> (Integer, Integer)
decode_tid_fn fn =
  case findIndex (=='.') fn of
    Nothing -> (0, 0)
    Just i -> let (tidstr, fnstr) = splitAt i fn in
      (read tidstr, read (tail fnstr))

data POP3Conn =
  POP3Conn Handle

data SMTPConn =
  SMTPConn Handle
