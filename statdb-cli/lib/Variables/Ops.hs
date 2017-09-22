module Variables.Ops where

import Control.Monad.State.Strict (gets, modify)
import Variables.State
import VariablesAPI
import Abstraction

init :: Proc InitResult
init = return Initialized

read :: Coq_var -> Proc Integer
read VarCount = gets varCount
read VarSum = gets varSum

write :: Coq_var -> Integer -> Proc ()
write VarCount x = modify (\s -> s { varCount = x })
write VarSum x = modify (\s -> s { varSum = x })
