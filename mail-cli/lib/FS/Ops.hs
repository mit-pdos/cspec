module FS.Ops where

import Control.Monad.State.Strict (gets, modify)
import Control.Monad.Trans (liftIO)

import FS.State
import FSAPI
import Abstraction

import String
import System.IO

import Data.Map.Strict

init :: Proc InitResult
init = return Initialized

create :: Coq_pathname -> String -> Proc Integer
create pn fn = do
  n <- gets nextH
  h <- liftIO $ do
    openFile fn WriteMode
  modify (\s -> s { nextH = n+1 })
  m <- gets storeH
  modify (\s -> s { storeH = (Data.Map.Strict.insert n h m) })
  -- liftIO $ do
  --  putStrLn $ "map:" ++ show m
  return n


mkdir :: Coq_pathname -> String -> Proc Integer
mkdir pn fn = gets nextH

-- XXX search
find_available_name :: Coq_pathname -> Proc String
find_available_name pn = return "xxx"

