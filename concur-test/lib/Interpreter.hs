module Interpreter where

-- Haskell libraries
import Control.Concurrent
import Data.Atomics
import Data.IORef
import Data.Maybe
import GHC.Base

-- Extracted code
import ConcurProc
import LockedCounter

data State =
  S !(IORef Integer) !(IORef Integer)

mkState :: IO State
mkState = do
  val0 <- newIORef 0
  val1 <- newIORef 0
  return $ S val0 val1

verbose :: Bool
verbose = True

debugmsg :: String -> IO ()
debugmsg s =
  if verbose then do
    tid <- myThreadId
    putStrLn $ "[" ++ (show tid) ++ "] " ++ s
  else
    return ()

run_proc :: State -> Coq_proc (TSOOp__Coq_xOp a) GHC.Base.Any -> IO a
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
run_proc (S val0 val1) (Call (TSOOp__Read TSOOp__Coq_addr0)) = do
  v <- readIORef val0
  return $ unsafeCoerce v
run_proc (S val0 val1) (Call (TSOOp__Read TSOOp__Coq_addr1)) = do
  v <- readIORef val1
  return $ unsafeCoerce v
run_proc (S val0 val1) (Call (TSOOp__Write TSOOp__Coq_addr0 v)) = do
  debugmsg $ "Write0 " ++ (show v)
  writeIORef val0 v
  return $ unsafeCoerce ()
run_proc (S val0 val1) (Call (TSOOp__Write TSOOp__Coq_addr1 v)) = do
  debugmsg $ "Write1 " ++ (show v)
  writeIORef val1 v
  return $ unsafeCoerce ()
run_proc (S val0 val1) (Call (TSOOp__TestAndSet TSOOp__Coq_addr0 v)) = do
  prev <- atomicModifyIORef val0 (\cur -> (v, cur))
  if v == prev then yield else return ()
  return $ unsafeCoerce prev
run_proc (S val0 val1) (Call (TSOOp__TestAndSet TSOOp__Coq_addr1 v)) = do
  prev <- atomicModifyIORef val1 (\cur -> (v, cur))
  if v == prev then yield else return ()
  return $ unsafeCoerce prev
run_proc _ (Call TSOOp__Fence) = do
  -- we don't actually have weak memory (in fact Haskell does not define a
  -- memory model for IORefs), but if we had intrinsics we would call MFENCE
  return $ unsafeCoerce ()
