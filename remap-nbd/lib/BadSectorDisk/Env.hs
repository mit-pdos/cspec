module BadSectorDisk.Env
  (
    TheProc
  , Env
  , diskHandle
  , badSector
  , requests
  , responses
  , newEnv
  , runBS
  , (>>=)
  , return
  ) where

import Control.Concurrent.MVar (MVar, newEmptyMVar)
import Control.Monad.Reader (ReaderT, runReaderT)
import NbdAPI
import System.Directory (doesFileExist)
import System.IO.Error
import System.Posix.IO
import System.Posix.Types

data Env =
  Env { diskHandle :: Fd
      , badSector :: Integer
      , requests :: MVar Request
      , responses :: MVar Response }

type TheProc = ReaderT Env IO

newEnv :: FilePath -> Integer -> IO Env
newEnv fn badSectorArg = pure Env
  <*> openFile fn
  <*> return badSectorArg
  <*> newEmptyMVar <*> newEmptyMVar
  where openFile :: FilePath -> IO Fd
        openFile path = openFd path ReadWrite Nothing defaultFileFlags

runBS :: Env -> TheProc a -> IO a
runBS e m = runReaderT m e
