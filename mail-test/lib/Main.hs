{-# OPTIONS_GHC -F -pgmF ./fiximports.py #-}
module Main where

-- Haskell libraries
import Control.Concurrent

-- Our library code
import Interpreter

-- Extracted code
import ConcurProc
import MailFSPathAPI
import MailServer


run_thread :: Coq_maybe_proc (MailFSPathAPI__Coq_xopT a) -> IO ()
run_thread NoProc = return ()
run_thread (Proc p) = do
  tid <- myThreadId
  putStrLn $ "Running " ++ (show tid)

  s <- mkState
  run_proc s p
  return ()

spawn_thread :: Coq_maybe_proc (MailFSPathAPI__Coq_xopT a) -> IO ()
spawn_thread p = do
  putStrLn $ "Spawning.."
  tid <- forkIO (run_thread p)
  putStrLn $ "Spawned " ++ (show tid)
  return ()

main :: IO ()
main = do
  mapM_ spawn_thread (ms_bottom 4)
  putStrLn "Started all threads"
  threadDelay $ 60 * 1000000
