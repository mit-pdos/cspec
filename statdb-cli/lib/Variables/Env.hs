module Variables.Env
  (
    TheProc
  , varCount
  , varSum
  , newEnv
  , runVars
  , (>>=)
  , return
  ) where

import Control.Monad.Reader (ReaderT, runReaderT)
import Data.IORef

data Env =
  Env { varCount :: IORef Integer
      , varSum   :: IORef Integer }

type TheProc = ReaderT Env IO

newEnv :: IO Env
newEnv = do
  vc <- newIORef 0
  vs <- newIORef 1
  return $ Env vc vs

runVars :: Env -> TheProc a -> IO a
runVars e m = runReaderT m e
