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

-- TODO: support initializing with only one disk; currently openFd throws an
-- exception "does not exist"

data Env =
  Env { disk0 :: (FilePath, Fd)
      , disk1 :: (FilePath, Fd)
      , requests :: MVar Request
      , responses :: MVar Response }

type TwoDiskProg = ReaderT Env IO

newEnv :: FilePath -> FilePath -> IO Env
newEnv fn0 fn1 = pure Env
  <*> openFile fn0
  <*> openFile fn1
  <*> newEmptyMVar <*> newEmptyMVar
  where openFile :: FilePath -> IO (FilePath, Fd)
        openFile path = do
          fd <- openFd path ReadWrite Nothing defaultFileFlags
          return (path, fd)

runTD :: Env -> TwoDiskProg a -> IO a
runTD e m = runReaderT m e
