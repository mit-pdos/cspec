{-# OPTIONS_GHC -F -pgmF ./fiximports.py #-}
module Main where

-- Haskell libraries
import Control.Concurrent
import Control.Monad
import System.Environment
import System.Posix.Process

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
  pid <- getProcessID
  putStrLn $ "Running " ++ (show pid)

  s <- mkState smtp pop3
  run_proc s p
  return ()

main :: IO ()
main = do
  args <- getArgs
  mainArgs args

mainArgs :: [String] -> IO ()
mainArgs [nprocs, niter, nsmtpiter, npop3iter] = do
  smtp <- smtpListen 2525
  pop3 <- pop3Listen 2110
  pids <- mapM
    (\p -> forkProcess (run_thread smtp pop3 p))
    (ms_bottom (read nprocs) (read niter) (read nsmtpiter) (read npop3iter))
  putStrLn "Waiting for child processes.."
  mapM_ (getProcessStatus True False) pids
  putStrLn "Looping forever..."
  forever $ return ()

mainArgs _ = do
  exec <- getProgName
  putStrLn $ "Usage: " ++ exec ++ " nsmtp npop3"
