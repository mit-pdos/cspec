module Replication.TwoDiskEnvironment
  (
    TwoDiskProg
  , Env(..)
  , runTD
  , (>>=)
  , return
  ) where

import NbdData
import Control.Monad.Reader (ReaderT, runReaderT)
import Control.Concurrent.MVar (MVar)

data Env =
  Env { disk0Path :: FilePath
      , disk1Path :: FilePath
      , requests :: MVar Request
      , responses :: MVar Response }

type TwoDiskProg = ReaderT Env IO

runTD :: Env -> TwoDiskProg a -> IO a
runTD e m = runReaderT m e
