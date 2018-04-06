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

spawn_thread :: SMTPServer -> POP3Server -> Coq_maybe_proc (MailFSMergedOp__Coq_xopT a) -> MVar () -> IO ()
spawn_thread smtp pop3 p completion = do
  putStrLn $ "Spawning.."
  tid <- forkFinally (run_thread smtp pop3 p) (\_ -> putMVar completion ())
  putStrLn $ "Spawned " ++ (show tid)
  return ()

main :: IO ()
main = do
  args <- getArgs
  mainArgs args

mainArgs :: [String] -> IO ()
mainArgs [nsmtp, npop3, nsmtpiter, npop3iter] = do
  smtp <- smtpListen 2525
  pop3 <- pop3Listen 2110
  completions <- mapM
    (\p -> do
      completion <- newEmptyMVar;
      spawn_thread smtp pop3 p completion;
      return completion)
    (ms_bottom (read nsmtp) (read npop3) (read nsmtpiter) (read npop3iter))
  -- s <- mkState smtp pop3
  -- run_proc1 s (Proc (do_smtp "u1" "msg"))
  putStrLn "Started all threads"
  mapM_ takeMVar completions

mainArgs _ = do
  exec <- getProgName
  putStrLn $ "Usage: " ++ exec ++ " nsmtp npop3"
