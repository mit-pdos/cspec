module FS.State
  (
    Proc
  , FSState(..)
  , runFS
  , (>>=)
  , return
  ) where

import Control.Monad.State.Strict (StateT, evalStateT)
import Data.Map.Strict
import System.IO

data FSState =
  FS { storeH :: (Data.Map.Strict.Map Integer Handle)
       , nextH :: Integer}

type Proc = StateT FSState IO

initialEnv :: FSState
initialEnv = FS (Data.Map.Strict.empty) (0)

runFS :: Proc a -> IO a
runFS m = evalStateT m initialEnv
