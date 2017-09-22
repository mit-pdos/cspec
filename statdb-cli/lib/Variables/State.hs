module Variables.State
  (
    Proc
  , Vars(..)
  , runVars
  , (>>=)
  , return
  ) where

import Control.Monad.State.Strict (StateT, evalStateT)

data Vars =
  Vars { varCount :: Integer
       , varSum   :: Integer }

type Proc = StateT Vars IO

initialEnv :: Vars
initialEnv = Vars 0 0

runVars :: Proc a -> IO a
runVars m = evalStateT m initialEnv
