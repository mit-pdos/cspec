module FS.Ops where

import Control.Monad.State.Strict (gets, modify)
import Control.Monad.Trans (liftIO)

import FS.State
import FSAPI
import Abstraction

import String
import System.IO
import System.Directory
import System.FilePath.Posix

import Data.Map.Strict

verbose :: Bool
verbose = True

debugmsg :: String -> Proc ()
debugmsg s =
  liftIO $ do
    if verbose then
      do 
        putStrLn s
        hFlush stdout
    else
      return ()

init :: Proc InitResult
init = return Initialized

create :: Coq_pathname -> String -> Proc Integer
create cpn fn = do
  debugmsg $ "create: " ++ (show cpn) ++ " " ++ fn
  let pn = (joinPath cpn)
  _ <- liftIO $ do
    h <- openFile (pn++"/"++fn) WriteMode
    hClose h
  debugmsg $ "create done"
  return 0

-- mkdir -p
mkdir :: Coq_pathname -> String -> Proc Integer
mkdir cpn fn = do
  debugmsg $ "mkdir: " ++ (show cpn) ++ " " ++ fn
  let pn = (concat cpn)
  h <- liftIO $ do
    createDirectoryIfMissing True (pn++"/"++fn)
  debugmsg $ "mkdir done"
  return 0

write_logged :: Coq_pathname -> String -> Proc ()
write_logged cpn content = do
  debugmsg $ "write_logged: " ++ (show cpn) ++ " " ++ content
  let pn = (concat cpn)
  debugmsg $ "pn: " ++ pn
  h <- liftIO $ do
    writeFile pn content
  debugmsg $ "write done"
  return ()


debug :: String -> Proc ()
debug msg = do
  debugmsg $ "debug: " ++ msg


-- XXX search
find_available_name :: Coq_pathname -> Proc String
find_available_name pn = return "xxx"

