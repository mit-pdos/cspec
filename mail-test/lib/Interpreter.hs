module Interpreter where

-- Haskell libraries
import Control.Concurrent
import Data.Atomics
import Data.IORef
import Data.Maybe
import GHC.Prim

-- Extracted code
import ConcurProc
import MailFSPathAPI
import MailServer
import MailServerAPI

data State =
  S

mkState :: IO State
mkState = do
  return $ S

verbose :: Bool
verbose = True

debugmsg :: String -> IO ()
debugmsg s =
  if verbose then do
    tid <- myThreadId
    putStrLn $ "[" ++ (show tid) ++ "] " ++ s
  else
    return ()

run_proc :: State -> Coq_proc (MailFSPathAPI__Coq_xopT a) GHC.Prim.Any -> IO a
run_proc s (Ret v) = do
  -- debugmsg $ "Ret"
  return $ unsafeCoerce v
run_proc s (Bind p1 p2) = do
  -- debugmsg $ "Bind"
  v1 <- run_proc s p1
  v2 <- run_proc s (p2 $ unsafeCoerce v1)
  return v2
run_proc s (Atomic _) = do
  -- debugmsg $ "Atomic"
  error "Running atomic"
run_proc s (Until c p v0) = do
  -- debugmsg $ "Until"
  v <- run_proc s (p v0)
  if (c $ unsafeCoerce v) then
    return v
  else
    run_proc s (Until c p (unsafeCoerce v))

run_proc _ (Op MailFSPathAPI__GetTID) = do
  -- XXX how to get an integer thread id?
  return $ unsafeCoerce 0

run_proc _ (Op MailFSPathAPI__GetRequest) = do
  debugmsg $ "GetRequest"
  return $ unsafeCoerce (MailServerAPI__ReqDeliver "Test message")

run_proc _ (Op (MailFSPathAPI__Respond _)) = do
  debugmsg $ "Respond"
  return $ unsafeCoerce ()

run_proc _ (Op (MailFSPathAPI__CreateWrite (dir, fn) contents)) = do
  debugmsg $ "CreateWrite " ++ dir ++ "/" ++ fn ++ ", " ++ (show contents)
  return $ unsafeCoerce ()

run_proc _ (Op (MailFSPathAPI__Link (srcdir, srcfn) (dstdir, dstfn))) = do
  debugmsg $ "Link " ++ srcdir ++ "/" ++ srcfn ++ " to " ++ dstdir ++ "/" ++ dstfn
  return $ unsafeCoerce ()

run_proc _ (Op (MailFSPathAPI__Unlink (dir, fn))) = do
  debugmsg $ "Unlink " ++ dir ++ "/" ++ (fn)
  return $ unsafeCoerce ()

run_proc _ (Op (MailFSPathAPI__List dir)) = do
  debugmsg $ "List " ++ dir
  return $ unsafeCoerce []

run_proc _ (Op (MailFSPathAPI__Read (dir, fn))) = do
  debugmsg $ "Read " ++ dir ++ "/" ++ fn
  return $ unsafeCoerce ""