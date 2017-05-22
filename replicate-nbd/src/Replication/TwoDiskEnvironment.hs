module Replication.TwoDiskEnvironment
  (
    TwoDiskProg
  , Config(..)
  , runTD
  , (>>=)
  , return
  ) where

import Control.Monad.Reader (ReaderT, runReaderT)

data Config =
  Config { disk0Path :: FilePath
         , disk1Path :: FilePath }

type TwoDiskProg = ReaderT Config IO

runTD :: Config -> TwoDiskProg a -> IO a
runTD c m = runReaderT m c
