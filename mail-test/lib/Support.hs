module Support where

import Data.List

encode_tid_fn :: Integer -> String -> String
encode_tid_fn tid fn = (show tid) ++ "." ++ fn

decode_tid_fn :: String -> (Integer, String)
decode_tid_fn fn =
  case findIndex (=='.') fn of
    Nothing -> (0, fn)
    Just i -> let (tidstr, fnstr) = splitAt i fn in
      (read tidstr, tail fnstr)
