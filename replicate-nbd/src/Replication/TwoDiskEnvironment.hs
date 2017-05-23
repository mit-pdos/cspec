module Replication.TwoDiskEnvironment
  (
    TwoDiskProg
  , Env(..)
  , runTD
  , (>>=)
  , return
  ) where

import Control.Monad.Reader (ReaderT, runReaderT)

data Env =
  Env { disk0Path :: FilePath
      , disk1Path :: FilePath }

type TwoDiskProg = ReaderT Env IO

runTD :: Env -> TwoDiskProg a -> IO a
runTD e m = runReaderT m e
