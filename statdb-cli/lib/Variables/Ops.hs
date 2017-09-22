module Variables.Ops where

import Control.Monad.Reader (reader, liftIO)
import Data.IORef
import Variables.Env
import VariablesAPI
import Abstraction

getVar :: Coq_var -> Proc (IORef Integer)
getVar VarCount = reader varCount
getVar VarSum = reader varSum

init :: Proc InitResult
init = do
  return Initialized

read :: Coq_var -> Proc Integer
read v = do
  ref <- getVar v
  liftIO $ readIORef ref

write :: Coq_var -> Integer -> Proc ()
write v x = do
  ref <- getVar v
  liftIO $ writeIORef ref x
