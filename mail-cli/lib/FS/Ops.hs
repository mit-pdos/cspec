module FS.Ops where

import Control.Monad.State.Strict (gets, modify)

import FS.State
import FSAPI
import Abstraction

import String
import System.IO

init :: Proc InitResult
init = return Initialized

create :: Coq_pathname -> String -> Proc Integer
create pn fn = gets nextH

-- do
--  n <- 
--  return n

---   h <- openFile fn WriteMode
-- need to implement others