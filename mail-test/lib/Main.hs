{-# OPTIONS_GHC -F -pgmF ./fiximports.py #-}
module Main where

-- Haskell libraries
import Control.Concurrent
import Control.Monad
import System.Environment

-- Our library code
import Interpreter
import SMTP
import POP3

-- Extracted code
import ConcurProc
import MailFSMergedAPI
import MailServer


run_thread :: SMTPServer -> POP3Server -> Coq_maybe_proc (MailFSMergedOp__Coq_xopT a) -> IO ()
run_thread _ _ NoProc = return ()
run_thread smtp pop3 (Proc p) = do
  tid <- myThreadId
  putStrLn $ "Running " ++ (show tid)

  s <- mkState smtp pop3
  run_proc s p
  return ()

spawn_thread :: SMTPServer -> POP3Server -> Coq_maybe_proc (MailFSMergedOp__Coq_xopT a) -> IO ()
spawn_thread smtp pop3 p = do
  putStrLn $ "Spawning.."
  tid <- forkIO (run_thread smtp pop3 p)
  putStrLn $ "Spawned " ++ (show tid)
  return ()

main :: IO ()
main = do
  args <- getArgs
  mainArgs args

mainArgs :: [String] -> IO ()
mainArgs [nsmtp, npop3] = do
  smtp <- smtpListen 2525
  pop3 <- pop3Listen 2110
  mapM_ (spawn_thread smtp pop3) (ms_bottom (read nsmtp) (read npop3))
  putStrLn "Started all threads"
  forever $ threadDelay 1000000

mainArgs _ = do
  exec <- getProgName
  putStrLn $ "Usage: " ++ exec ++ " nsmtp npop3"
