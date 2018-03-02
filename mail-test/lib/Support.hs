module Support where

encode_tid_fn :: Integer -> String -> String
encode_tid_fn tid fn = (show tid) ++ "." ++ fn
