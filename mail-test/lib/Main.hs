{-# OPTIONS_GHC -F -pgmF ./fiximports.py #-}
module Main where

-- Haskell libraries
import Control.Concurrent

-- Our library code
import Interpreter
import SMTP

-- Extracted code
import ConcurProc
import MailFSPathAPI
import MailServer


run_thread :: SMTPServer -> Coq_maybe_proc (MailFSPathAPI__Coq_xopT a) -> IO ()
run_thread _ NoProc = return ()
run_thread smtp (Proc p) = do
  tid <- myThreadId
  putStrLn $ "Running " ++ (show tid)

  s <- mkState smtp
  run_proc s p
  return ()

spawn_thread :: SMTPServer -> Coq_maybe_proc (MailFSPathAPI__Coq_xopT a) -> IO ()
spawn_thread smtp p = do
  putStrLn $ "Spawning.."
  tid <- forkIO (run_thread smtp p)
  putStrLn $ "Spawned " ++ (show tid)
  return ()

main :: IO ()
main = do
  smtp <- smtpListen 2525
  mapM_ (spawn_thread smtp) (ms_bottom 4)
  putStrLn "Started all threads"
  threadDelay $ 60 * 1000000
