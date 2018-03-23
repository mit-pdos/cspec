module Interpreter where

-- Haskell libraries
import Control.Concurrent
import Data.Atomics
import Data.IORef
import Data.Maybe
import GHC.Prim

-- Extracted code
import ConcurProc
import Example2

data State =
  S !(MVar ()) !(IORef Integer)

mkState :: IO State
mkState = do
  lck <- newMVar ()
  val <- newIORef 0
  return $ S lck val

verbose :: Bool
verbose = True

debugmsg :: String -> IO ()
debugmsg s =
  if verbose then do
    tid <- myThreadId
    putStrLn $ "[" ++ (show tid) ++ "] " ++ s
  else
    return ()

run_proc :: State -> Coq_proc (TASOp__Coq_xopT a) GHC.Prim.Any -> IO a
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
run_proc (S lck val) (Op TASOp__ReadTAS) = do
  v <- readIORef val
  -- debugmsg $ "ReadTAS " ++ (show v)
  return $ unsafeCoerce v
run_proc (S lck val) (Op (TASOp__WriteTAS v)) = do
  debugmsg $ "WriteTAS " ++ (show v)
  writeIORef val v
  return $ unsafeCoerce ()
run_proc (S lck val) (Op TASOp__TestAndSet) = do
  ok <- tryTakeMVar lck
  -- debugmsg $ "TestAndSet " ++ (show ok)
  if isJust ok then
    return $ unsafeCoerce False
  else do
    yield
    return $ unsafeCoerce True
run_proc (S lck val) (Op TASOp__Clear) = do
  -- debugmsg $ "Clear"
  tryPutMVar lck ()
  return $ unsafeCoerce ()
