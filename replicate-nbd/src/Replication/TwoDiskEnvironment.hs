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
import System.Posix.Types
import System.Posix.IO

data Env =
  Env { disk0Fd :: Fd
      , disk1Fd :: Fd
      , requests :: MVar Request
      , responses :: MVar Response }

type TwoDiskProg = ReaderT Env IO

newEnv :: FilePath -> FilePath -> IO Env
newEnv fn0 fn1 = pure Env
  <*> openFile fn0 <*> openFile fn1
  <*> newEmptyMVar <*> newEmptyMVar
  where openFile :: FilePath -> IO Fd
        openFile path = openFd path ReadWrite Nothing defaultFileFlags

runTD :: Env -> TwoDiskProg a -> IO a
runTD e m = runReaderT m e
