module Interpreter where

-- Haskell libraries
import Data.Atomics
import Data.IORef
import GHC.Prim

-- Extracted code
import ConcurProc
import Example2

data State =
  S !(IORef Bool) !(IORef Integer)

mkState :: IO State
mkState = do
  lck <- newIORef $ False
  val <- newIORef $ 0
  return $ S lck val

verbose :: Bool
verbose = True

debugmsg :: String -> IO ()
debugmsg s =
  if verbose then
    putStrLn s
  else
    return ()

run_proc :: State -> Coq_proc (TASOpT a) GHC.Prim.Any -> IO a
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
run_proc s (Log v) = do
  -- debugmsg $ "Log"
  return $ unsafeCoerce v
run_proc s (Until c p) = do
  -- debugmsg $ "Until"
  v <- run_proc s p
  if (c $ unsafeCoerce v) then
    return v
  else
    run_proc s (Until c p)
run_proc (S lck val) (Op ReadTAS) = do
  v <- readIORef val
  debugmsg $ "ReadTAS " ++ (show v)
  return $ unsafeCoerce v
run_proc (S lck val) (Op (WriteTAS v)) = do
  debugmsg $ "WriteTAS " ++ (show v)
  writeIORef val v
  return $ unsafeCoerce ()
run_proc (S lck val) (Op TestAndSet) = do
  tkt <- readForCAS lck
  debugmsg $ "TestAndSet " ++ (show $ peekTicket tkt)
  if peekTicket tkt == False then do
    (ok, _) <- casIORef lck tkt True
    if ok then
      return $ unsafeCoerce False
    else
      return $ unsafeCoerce True
  else
    return $ unsafeCoerce True
run_proc (S lck val) (Op Clear) = do
  debugmsg $ "Clear"
  writeIORef lck False
  return $ unsafeCoerce ()
