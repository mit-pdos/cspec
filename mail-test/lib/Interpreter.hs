module Interpreter where

-- Haskell libraries
import Control.Concurrent
import Control.DeepSeq
import Control.Exception
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC8
import GHC.Base
import System.Posix.Files
import System.Posix.IO
import System.Directory
import System.IO
import System.IO.Error
import System.CPUTime.Rdtsc
import System.Lock.FLock
import System.Posix.Process

-- Our own libraries
import SMTP
import POP3

-- Extracted code
import ConcurProc
import qualified Horizontal
import MailFSMergedAPI
import MailServer
import MailServerAPI

-- State for each process/thread
data State =
  S Integer SMTPServer POP3Server !(MVar Lock)

mkState :: SMTPServer -> POP3Server -> IO State
mkState smtp pop3 = do
  lockvar <- newEmptyMVar
  pid <- getProcessID
  return $ S (fromIntegral pid) smtp pop3 lockvar

verbose :: Bool
verbose = False

showBS :: Show a => a -> BS.ByteString
showBS = BSC8.pack . show

debugmsg :: BS.ByteString -> IO ()
debugmsg s =
  when verbose $ do
    tid <- myThreadId
    BSC8.putStrLn $ BS.concat ["[", showBS tid, "] ", s]

debugmsgs :: [BS.ByteString] -> IO ()
debugmsgs = debugmsg . BS.concat

userPath :: BS.ByteString -> String
userPath u = "/tmp/mailtest/" ++ BSC8.unpack u

dirPath :: BS.ByteString -> BS.ByteString -> String
dirPath u dir = userPath u ++ "/" ++ BSC8.unpack dir

filePath :: BS.ByteString -> BS.ByteString -> BS.ByteString -> FilePath
filePath u dir fn = dirPath u dir ++ "/" ++ BSC8.unpack fn

run_proc :: State -> Coq_proc (MailFSMergedOp__Coq_xOp a) GHC.Base.Any -> IO a
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
  debugmsg $ "Until"
  v <- run_proc s (p v0)
  if (c $ unsafeCoerce v) then do
    debugmsg $ "Until true"
    return v
  else do
    debugmsg $ "Until false"
    run_proc s (Until c p (unsafeCoerce (Just v)))
run_proc s (Spawn p) = do
  debugmsg "Spawn"
  _ <- forkProcess $ do
    pid <- getProcessID
    putStrLn $ "Spawned " ++ show pid
    _ <- run_proc s p
    return ()
  return $ unsafeCoerce ()

run_proc (S tid _ _ _) (Call MailFSMergedOp__GetTID) = do
  return $ unsafeCoerce tid

run_proc _ (Call MailFSMergedOp__Random) = do
  ts <- rdtsc
  return $ unsafeCoerce (fromIntegral ts :: Integer)

run_proc _ (Call (MailFSMergedOp__Ext (MailServerOp__PickUser))) = do
  debugmsg $ "PickUser"
  u <- rdtsc
  return $ unsafeCoerce $ "u" ++ (show $ u `mod` 100)

run_proc (S _ smtpserver _ _) (Call (MailFSMergedOp__Ext (MailServerOp__AcceptSMTP))) = do
  debugmsg $ "AcceptSMTP"
  conn <- smtpAccept smtpserver
  return $ unsafeCoerce conn

run_proc (S _ _ pop3server _) (Call (MailFSMergedOp__Ext (MailServerOp__AcceptPOP3))) = do
  debugmsg $ "AcceptPOP3"
  conn <- pop3Accept pop3server
  return $ unsafeCoerce conn

run_proc _ (Call (MailFSMergedOp__Ext (MailServerOp__SMTPGetMessage conn))) = do
  debugmsg $ "SMTPGetMessage"
  msg <- smtpGetMessage conn
  return $ unsafeCoerce msg

run_proc _ (Call (MailFSMergedOp__Ext (MailServerOp__SMTPRespond conn ok))) = do
  debugmsgs ["SMTPRespond", " ", showBS ok]
  smtpDone conn ok
  return $ unsafeCoerce ()

run_proc _ (Call (MailFSMergedOp__Ext (MailServerOp__POP3Authenticate conn))) = do
  debugmsg $ "POP3Authenticate"
  req <- pop3Authenticate conn
  return $ unsafeCoerce req

run_proc _ (Call (MailFSMergedOp__Ext (MailServerOp__POP3RespondAuth conn eok))) = do
  debugmsg $ "POP3RespondAuth"
  pop3RespondAuth conn eok
  return $ unsafeCoerce ()

run_proc _ (Call (MailFSMergedOp__Ext (MailServerOp__POP3GetRequest conn))) = do
  debugmsg $ "POP3GetRequest"
  req <- pop3GetRequest conn
  return $ unsafeCoerce req

run_proc _ (Call (MailFSMergedOp__Ext (MailServerOp__POP3RespondStat conn count bytes))) = do
  debugmsg $ "POP3RespondStat"
  pop3RespondStat conn count bytes
  return $ unsafeCoerce ()

run_proc _ (Call (MailFSMergedOp__Ext (MailServerOp__POP3RespondList conn msglens))) = do
  debugmsg $ "POP3RespondList"
  pop3RespondList conn msglens
  return $ unsafeCoerce ()

run_proc _ (Call (MailFSMergedOp__Ext (MailServerOp__POP3RespondRetr conn body))) = do
  debugmsg $ "POP3RespondRetr"
  pop3RespondRetr conn body
  return $ unsafeCoerce ()

run_proc _ (Call (MailFSMergedOp__Ext (MailServerOp__POP3RespondDelete conn))) = do
  debugmsg $ "POP3RespondDelete"
  pop3RespondDelete conn
  return $ unsafeCoerce ()

run_proc _ (Call (MailFSMergedOp__CreateWrite ((u, dir), fn) contents)) = do
  debugmsgs ["CreateWrite ", u, "/", dir, "/", fn, ", ", showBS contents]
  catch (do
           BS.writeFile (filePath u dir fn) contents
           return $ unsafeCoerce True)
        (\e -> case e of
               _ | isFullError e -> do
                 debugmsg "Out of space on createwrite"
                 return $ unsafeCoerce False
               _ -> do
                 debugmsg "Unknown exception on createwrite"
                 return $ unsafeCoerce False)

run_proc _ (Call (MailFSMergedOp__Link ((srcu, srcdir), srcfn) ((dstu, dstdir), dstfn))) = do
  debugmsgs ["Link ", srcu, "/", srcdir, "/", srcfn, " to ", dstu, "/", dstdir, "/", dstfn]
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

run_proc _ (Call (MailFSMergedOp__Unlink ((u, dir), fn))) = do
  debugmsgs ["Unlink ", u, "/", dir, "/", fn]
  catch (removeLink (filePath u dir fn))
        (\e -> case e of
           _ | isDoesNotExistError e -> do
             debugmsg "removeLink does not exist"
             return ()
           _ -> do
             debugmsg "removeLink error"
             return ())
  return $ unsafeCoerce ()

run_proc _ (Call (MailFSMergedOp__List (u, dir))) = do
  debugmsgs ["List ", u, "/", dir]
  files <- listDirectory (dirPath u dir)
  return $ unsafeCoerce files

run_proc _ (Call (MailFSMergedOp__Read ((u, dir), fn))) = do
  debugmsgs ["Read ", u, "/", dir, "/", fn]
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

run_proc (S _ _ _ lockvar) (Call (MailFSMergedOp__Lock u)) = do
  debugmsgs ["Lock ", u]
  mboxfd <- openFd (dirPath u "mail") ReadOnly Nothing defaultFileFlags
  lck <- lockFd mboxfd Exclusive Block
  closeFd mboxfd
  putMVar lockvar lck
  return $ unsafeCoerce ()

run_proc (S _ _ _ lockvar) (Call (MailFSMergedOp__Unlock u)) = do
  debugmsgs ["Unlock ", u]
  lck <- takeMVar lockvar
  unlock lck
  return $ unsafeCoerce ()

run_proc _ (Call (MailFSMergedOp__Exists u)) = do
  debugmsgs ["Exists ", u]
  ok <- fileExist (userPath u)
  if ok then do
    return $ unsafeCoerce (Horizontal.Present u)
  else do
    return $ unsafeCoerce Horizontal.Missing
