module Interpreter where

-- Haskell libraries
import Control.Concurrent
import Control.DeepSeq
import Control.Exception
import Data.Atomics
import Data.IORef
import Data.Maybe
import GHC.Prim
import System.Posix.Files
import System.Posix.IO
import System.Directory
import System.Random
import System.IO
import System.IO.Error
import System.CPUTime.Rdtsc
import System.Lock.FLock

-- Our own libraries
import Support
import SMTP
import POP3

-- Extracted code
import ConcurProc
import MailFSMergedAPI
import MailServer
import MailServerAPI

-- State for each process/thread
data State =
  S SMTPServer POP3Server !(MVar Lock)

mkState :: SMTPServer -> POP3Server -> IO State
mkState smtp pop3 = do
  lockvar <- newEmptyMVar
  return $ S smtp pop3 lockvar

verbose :: Bool
verbose = True

debugmsg :: String -> IO ()
debugmsg s =
  if verbose then do
    tid <- myThreadId
    putStrLn $ "[" ++ (show tid) ++ "] " ++ s
  else
    return ()

userPath :: String -> String
userPath u = "/tmp/mailtest/" ++ u

dirPath :: String -> String -> String
dirPath u dir = (userPath u) ++ "/" ++ dir

filePath :: String -> String -> String -> String
filePath u dir fn = (dirPath u dir) ++ "/" ++ fn

run_proc :: State -> Coq_proc (MailFSMergedOp__Coq_xopT a) GHC.Prim.Any -> IO a
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

run_proc _ (Op MailFSMergedOp__GetTID) = do
  tid <- myThreadId
  -- Horrible hack: get the numeric TID by printing the ThreadId as a string,
  -- using [show], which returns something like "ThreadId 5", and then parse
  -- it back to Integer using [read].
  let (_, tidstr) = splitAt 9 (show tid) in do
    return $ unsafeCoerce (read tidstr :: Integer)

run_proc _ (Op MailFSMergedOp__Random) = do
  ts <- rdtsc
  return $ unsafeCoerce (fromIntegral ts :: Integer)

run_proc (S smtpserver _ _) (Op (MailFSMergedOp__Ext (MailServerOp__AcceptSMTP))) = do
  debugmsg $ "AcceptSMTP"
  conn <- smtpAccept smtpserver
  return $ unsafeCoerce conn

run_proc (S _ pop3server _) (Op (MailFSMergedOp__Ext (MailServerOp__AcceptPOP3))) = do
  debugmsg $ "AcceptPOP3"
  conn <- pop3Accept pop3server
  return $ unsafeCoerce conn

run_proc _ (Op (MailFSMergedOp__Ext (MailServerOp__SMTPGetMessage conn))) = do
  debugmsg $ "SMTPGetMessage"
  msg <- smtpGetMessage conn
  return $ unsafeCoerce msg

run_proc _ (Op (MailFSMergedOp__Ext (MailServerOp__SMTPRespond conn ok))) = do
  debugmsg $ "SMTPRespond" ++ " " ++ (show ok)
  smtpDone conn ok
  return $ unsafeCoerce ()

run_proc _ (Op (MailFSMergedOp__Ext (MailServerOp__POP3Authenticate conn))) = do
  debugmsg $ "POP3Authenticate"
  req <- pop3Authenticate conn
  return $ unsafeCoerce req

run_proc _ (Op (MailFSMergedOp__Ext (MailServerOp__POP3GetRequest conn))) = do
  debugmsg $ "POP3GetRequest"
  req <- pop3GetRequest conn
  return $ unsafeCoerce req

run_proc _ (Op (MailFSMergedOp__Ext (MailServerOp__POP3RespondStat conn count bytes))) = do
  debugmsg $ "POP3RespondStat"
  pop3RespondStat conn count bytes
  return $ unsafeCoerce ()

run_proc _ (Op (MailFSMergedOp__Ext (MailServerOp__POP3RespondList conn msglens))) = do
  debugmsg $ "POP3RespondList"
  pop3RespondList conn msglens
  return $ unsafeCoerce ()

run_proc _ (Op (MailFSMergedOp__Ext (MailServerOp__POP3RespondRetr conn body))) = do
  debugmsg $ "POP3RespondRetr"
  pop3RespondRetr conn body
  return $ unsafeCoerce ()

run_proc _ (Op (MailFSMergedOp__Ext (MailServerOp__POP3RespondDelete conn))) = do
  debugmsg $ "POP3RespondDelete"
  pop3RespondDelete conn
  return $ unsafeCoerce ()

run_proc _ (Op (MailFSMergedOp__CreateWrite ((u, dir), fn) contents)) = do
  debugmsg $ "CreateWrite " ++ u ++ "/" ++ dir ++ "/" ++ fn ++ ", " ++ (show contents)
  catch (do
           writeFile (filePath u dir fn) contents
           return $ unsafeCoerce True)
        (\e -> case e of
               _ | isFullError e -> do
                 debugmsg "Out of space on createwrite"
                 return $ unsafeCoerce False
               _ -> do
                 debugmsg "Unknown exception on createwrite"
                 return $ unsafeCoerce False)

run_proc _ (Op (MailFSMergedOp__Link ((srcu, srcdir), srcfn) ((dstu, dstdir), dstfn))) = do
  debugmsg $ "Link " ++ srcu ++ "/" ++ srcdir ++ "/" ++ srcfn ++ " to " ++ dstu ++ "/" ++ dstdir ++ "/" ++ dstfn
  catch (do
           createLink (filePath srcu srcdir srcfn) (filePath dstu dstdir dstfn)
           return $ unsafeCoerce True)
        (\e -> case e of
               _ | isAlreadyExistsError e -> do
                 debugmsg "createLink already exists"
                 return $ unsafeCoerce False
               _ -> do
                 debugmsg "createLink unknown error"
                 return $ unsafeCoerce False)

run_proc _ (Op (MailFSMergedOp__Unlink ((u, dir), fn))) = do
  debugmsg $ "Unlink " ++ u ++ "/" ++ dir ++ "/" ++ (fn)
  catch (removeLink (filePath u dir fn))
        (\e -> case e of
           _ | isDoesNotExistError e -> do
             debugmsg "removeLink does not exist"
             return ()
           _ -> do
             debugmsg "removeLink error"
             return ())
  return $ unsafeCoerce ()

run_proc _ (Op (MailFSMergedOp__List (u, dir))) = do
  debugmsg $ "List " ++ u ++ "/" ++ dir
  files <- listDirectory (dirPath u dir)
  return $ unsafeCoerce files

run_proc _ (Op (MailFSMergedOp__Read ((u, dir), fn))) = do
  debugmsg $ "Read " ++ u ++ "/" ++ dir ++ "/" ++ fn
  catch (do
           h <- openFile (filePath u dir fn) ReadMode
           contents <- hGetContents h
           evaluate (rnf contents)
           hClose h
           return $ unsafeCoerce (Just contents))
        (\e -> case e of
               _ | isDoesNotExistError e -> do
                 debugmsg "Reading a non-existant file"
                 return $ unsafeCoerce Nothing
               _ -> do
                 debugmsg "Unknown exception on read"
                 return $ unsafeCoerce Nothing)

run_proc (S _ _ lockvar) (Op (MailFSMergedOp__Lock u)) = do
  debugmsg $ "Lock " ++ u
  mboxfd <- openFd (dirPath u "mail") ReadOnly Nothing defaultFileFlags
  lck <- lockFd mboxfd Exclusive Block
  closeFd mboxfd
  putMVar lockvar lck
  return $ unsafeCoerce ()

run_proc (S _ _ lockvar) (Op (MailFSMergedOp__Unlock u)) = do
  debugmsg $ "Unlock " ++ u
  lck <- takeMVar lockvar
  unlock lck
  return $ unsafeCoerce ()

run_proc _ (Op (MailFSMergedOp__Exists u)) = do
  debugmsg $ "Exists " ++ u
  ok <- fileExist (userPath u)
  return $ unsafeCoerce ok
