module BadSectorDisk.Env
  (
    TheProg
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
import NbdData
import System.Directory (doesFileExist)
import System.IO.Error
import System.Posix.IO
import System.Posix.Types

data Env =
  Env { diskHandle :: Fd
      , badSector :: Integer
      , requests :: MVar Request
      , responses :: MVar Response }

type TheProg = ReaderT Env IO

newEnv :: FilePath -> Integer -> IO Env
newEnv fn badSectorArg = pure Env
  <*> openFile fn
  <*> return badSectorArg
  <*> newEmptyMVar <*> newEmptyMVar
  where openFile :: FilePath -> IO Fd
        openFile path = openFd path ReadWrite Nothing defaultFileFlags

runBS :: Env -> TheProg a -> IO a
runBS e m = runReaderT m e
