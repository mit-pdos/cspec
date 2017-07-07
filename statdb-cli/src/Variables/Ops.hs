module Variables.Ops where

import Control.Monad.Reader (reader, liftIO)
import Data.IORef
import Variables.Env
import VariablesAPI

getVar :: Vars__Coq_var -> TheProg (IORef Integer)
getVar Vars__VarCount = reader varCount
getVar Vars__VarSum = reader varSum

read :: Vars__Coq_var -> TheProg Integer
read v = do
  ref <- getVar v
  liftIO $ readIORef ref

write :: Vars__Coq_var -> Integer -> TheProg ()
write v x = do
  ref <- getVar v
  liftIO $ writeIORef ref x
