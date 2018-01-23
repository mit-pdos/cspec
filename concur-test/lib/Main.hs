{-# OPTIONS_GHC -F -pgmF ./fiximports.py #-}
module Main where

-- Haskell libraries
import Control.Concurrent

-- Our library code
import Interpreter

-- Extracted code
import ConcurProc
import Example2


run_thread :: State -> Coq_maybe_proc (TASOpT a) -> IO ()
run_thread _ NoProc = return ()
run_thread s (Proc p) = do
  run_proc s p
  return ()

spawn_thread :: State -> Coq_maybe_proc (TASOpT a) -> IO ()
spawn_thread s p = do
  putStrLn "Spawning.."
  forkIO (run_thread s p)
  return ()

main :: IO ()
main = do
  s <- mkState
  mapM_ (spawn_thread s) compiled_threads
  putStrLn "Started all threads"
  threadDelay $ 60 * 1000000
