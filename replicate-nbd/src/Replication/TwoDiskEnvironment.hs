module Replication.TwoDiskEnvironment
  (
    ReaderT
  , Config(..)
  , IO
  , (>>=)
  , return
  ) where

import Control.Monad.Reader (ReaderT)

data Config =
  Config { disk0Path :: FilePath
         , disk1Path :: FilePath }
