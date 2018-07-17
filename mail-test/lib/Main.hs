{-# OPTIONS_GHC -F -pgmF ./fiximports.py #-}
module Main where

-- Haskell libraries
import System.Environment

-- Our library code
import Interpreter
import SMTP
import POP3

-- Extracted code
import ConcurProc
import MailFSMergedAPI
import MailServer


runThread :: State -> Coq_maybe_proc (MailFSMergedOp__Coq_xOp a) -> IO ()
runThread _ NoProc = return ()
runThread s (Proc p) = do
  _ <- run_proc s p
  return ()

main :: IO ()
main = do
  args <- getArgs
  mainArgs args

mainArgs :: [String] -> IO ()
mainArgs [nprocs, niter, nsmtpiter, npop3iter] = do
  smtp <- smtpListen 2525
  pop3 <- pop3Listen 2110
  s <- mkState smtp pop3
  mapM_ (runThread s)
    (ms_bottom (read nprocs) (read niter) (read nsmtpiter) (read npop3iter))
  putStrLn "Waiting for child processes..."
  waitForChildren s

mainArgs _ = do
  exec <- getProgName
  putStrLn $ "Usage: " ++ exec ++ " nsmtp npop3"
