module Replication.TwoDiskEnvironment
  (
    TwoDiskProg
  , Env(..)
  , newEnv
  , runTD
  , (>>=)
  , return
  ) where

import NbdData
import Control.Monad.Reader (ReaderT, runReaderT)
import Control.Concurrent.MVar (MVar, newEmptyMVar)

data Env =
  Env { disk0Path :: FilePath
      , disk1Path :: FilePath
      , requests :: MVar Request
      , responses :: MVar Response }

type TwoDiskProg = ReaderT Env IO

newEnv :: FilePath -> FilePath -> IO Env
newEnv fn0 fn1 = Env fn0 fn1 <$> newEmptyMVar <*> newEmptyMVar

runTD :: Env -> TwoDiskProg a -> IO a
runTD e m = runReaderT m e
