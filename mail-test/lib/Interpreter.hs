{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PackageImports #-}
module Interpreter where

-- Haskell libraries
import Control.Concurrent
import Control.Exception
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC8
import GHC.Base
import System.Posix.ByteString.FilePath (RawFilePath)
import System.Posix.Files.ByteString (createLink, removeLink, fileExist)
import "unix" System.Posix.IO.ByteString (openFd, closeFd,
                                          defaultFileFlags, OpenFileFlags(..), OpenMode(..))
import "unix-bytestring" System.Posix.IO.ByteString (fdRead, fdWrite)
import System.Posix.Directory.ByteString (openDirStream, readDirStream, closeDirStream)
import System.IO.Error
import System.CPUTime.Rdtsc
import System.Lock.FLock
import System.Posix.Process (forkProcess, getProcessID, getProcessStatus, ProcessStatus(..))
import System.Posix.Types (ProcessID, Fd, FileMode)

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
  S { tid :: Integer
    , smtpserver :: SMTPServer
    , pop3server :: POP3Server
    , lockvar :: !(MVar Lock)
    , childrenRef :: MVar [ProcessID] }

mkState :: SMTPServer -> POP3Server -> IO State
mkState smtp pop3 = do
  lockvar <- newEmptyMVar
  pid <- getProcessID
  cref <- newMVar []
  return $ S (fromIntegral pid) smtp pop3 lockvar cref

waitForProcess :: ProcessID -> IO ()
waitForProcess pid = do
  mTc <- getProcessStatus True False pid
  case mTc of
    Just (Exited _) -> return ()
    Just (Terminated s _) -> putStrLn $ "process terminated by signal " ++ show s
    Just (Stopped _) -> BSC8.putStrLn "process stopped"
    Nothing -> BSC8.putStrLn "no status"

waitForChildren :: State -> IO ()
waitForChildren S{childrenRef} = do
  children <- readMVar childrenRef
  mapM_ (\pid -> do
            when verbose (putStrLn ("waiting for " ++ show pid))
            waitForProcess pid) children

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

userPath :: BS.ByteString -> BS.ByteString
userPath u = BS.concat ["/tmp/mailtest/", u]

dirPath :: BS.ByteString -> BS.ByteString -> RawFilePath
dirPath u dir = BS.concat [userPath u, "/", dir]

filePath :: BS.ByteString -> BS.ByteString -> BS.ByteString -> RawFilePath
filePath u dir fn = BS.concat [dirPath u dir, "/", fn]

pickUser :: IO BS.ByteString
pickUser = do
  u <- rdtsc
  return $ BS.concat ["u", BSC8.pack $ show (u `mod` 100)]

listDirectory :: RawFilePath -> IO [RawFilePath]
listDirectory p = bracket open close repeatRead
  where open = openDirStream p
        close = closeDirStream
        repeatRead stream = do
          d <- readDirStream stream
          if BS.null d
            then return []
            else if d == "." || d == ".." then repeatRead stream
            else (d:) <$> repeatRead stream

listMailDir :: BS.ByteString -> BS.ByteString -> IO [BS.ByteString]
listMailDir u dir = listDirectory (dirPath u dir)

withFd :: RawFilePath -> OpenMode -> Maybe FileMode -> (Fd -> IO a) -> IO a
withFd p m fm = bracket open close
  where open = openFd p m fm defaultFileFlags
        close = closeFd

withFdFlags :: RawFilePath -> OpenMode -> Maybe FileMode -> OpenFileFlags -> (Fd -> IO a) -> IO a
withFdFlags p m fm fdFlags = bracket open close
  where open = openFd p m fm fdFlags
        close = closeFd

readFileBytes :: RawFilePath -> IO BS.ByteString
readFileBytes p = withFd p ReadOnly Nothing $
  \fd -> let bytes = 4096
             go = do
              s <- fdRead fd bytes
              if BS.length s == fromIntegral bytes
                then BS.append s <$> go
                else return s in
          go

createFile :: RawFilePath -> IO ()
createFile p = withFdFlags p WriteOnly (Just 0o666) (defaultFileFlags { trunc = True }) $
  \fd -> return ()

writeFileBytes :: RawFilePath -> BS.ByteString -> IO ()
writeFileBytes p contents = withFd p WriteOnly (Just 0o666) $
  \fd -> let go s = do
              bytes <- fromIntegral <$> fdWrite fd s
              if bytes < BS.length s
                then go (BS.drop bytes s)
                else return () in
          go contents

readMail :: BS.ByteString -> BS.ByteString -> BS.ByteString -> IO BS.ByteString
readMail u dir fn = readFileBytes (filePath u dir fn)

{- TCB: run_proc implements the low-level operations used by the mail server.
 These implementations are trusted; specifically, they should be atomic with
 respect to one another and have the semantics specified in MailFSMergedAPI.v. -}
run_proc :: State -> Coq_proc (MailFSMergedOp__Coq_xOp a) GHC.Base.Any -> IO a
run_proc _ (Ret v) = do
  -- debugmsg $ "Ret"
  return $ unsafeCoerce v
run_proc s (Bind p1 p2) = {-# SCC "Bind" #-} do
  -- debugmsg $ "Bind"
  v1 <- run_proc s p1
  v2 <- run_proc s (p2 $ unsafeCoerce v1)
  return v2
run_proc _ (Atomic _) = do
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
run_proc s@S{childrenRef} (Spawn p) = do
  debugmsg "Spawn"
  child <- forkProcess $ do
    pid <- getProcessID
    putStrLn $ "Spawned " ++ show pid
    _ <- run_proc (s { tid = fromIntegral pid }) p
    return ()
  modifyMVar_ childrenRef (\l -> return $ child:l)
  return $ unsafeCoerce ()

run_proc S{tid} (Call MailFSMergedOp__GetTID) = do
  return $ unsafeCoerce tid

run_proc _ (Call MailFSMergedOp__Random) = do
  ts <- rdtsc
  return $ unsafeCoerce (fromIntegral ts :: Integer)

run_proc _ (Call (MailFSMergedOp__Ext (MailServerOp__PickUser))) = do
  debugmsg $ "PickUser"
  userDir <- pickUser
  return $ unsafeCoerce userDir

run_proc S{smtpserver} (Call (MailFSMergedOp__Ext (MailServerOp__AcceptSMTP))) = do
  debugmsg $ "AcceptSMTP"
  conn <- smtpAccept smtpserver
  return $ unsafeCoerce conn

run_proc S{pop3server} (Call (MailFSMergedOp__Ext (MailServerOp__AcceptPOP3))) = do
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

run_proc _ (Call (MailFSMergedOp__Create ((u, dir), fn))) = {-# SCC "Create" #-} do
  debugmsgs ["Create ", u, "/", dir, "/", fn]
  catch (do
           createFile (filePath u dir fn)
           return $ unsafeCoerce True)
        (\e -> case e of
               _ | isFullError e -> do
                 debugmsg "Out of space on create"
                 return $ unsafeCoerce False
               _ -> do
                 debugmsg "Unknown exception on create"
                 return $ unsafeCoerce False)

run_proc _ (Call (MailFSMergedOp__Write ((u, dir), fn) contents)) = {-# SCC "Write" #-} do
  debugmsgs ["Write ", u, "/", dir, "/", fn, ", ", showBS contents]
  catch (do
           writeFileBytes (filePath u dir fn) contents
           return $ unsafeCoerce True)
        (\e -> case e of
               _ | isFullError e -> do
                 debugmsg "Out of space on write"
                 return $ unsafeCoerce False
               _ -> do
                 debugmsg "Unknown exception on write"
                 return $ unsafeCoerce False)

run_proc _ (Call (MailFSMergedOp__Link ((srcu, srcdir), srcfn) ((dstu, dstdir), dstfn))) = {-# SCC "Link" #-} do
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

run_proc _ (Call (MailFSMergedOp__Unlink ((u, dir), fn))) = {-# SCC "Unlink" #-} do
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

run_proc _ (Call (MailFSMergedOp__List (u, dir))) = {-# SCC "List" #-} do
  debugmsgs ["List ", u, "/", dir]
  files <- listMailDir u dir
  return $ unsafeCoerce files

run_proc _ (Call (MailFSMergedOp__Read ((u, dir), fn))) = {-# SCC "Read" #-} do
  debugmsgs ["Read ", u, "/", dir, "/", fn]
  catch (do
           contents <- readMail u dir fn
           return $ unsafeCoerce (Just contents))
        (\e -> case e of
               _ | isDoesNotExistError e -> do
                 debugmsg "Reading a non-existant file"
                 return $ unsafeCoerce Nothing
               _ -> do
                 debugmsg "Unknown exception on read"
                 return $ unsafeCoerce Nothing)

run_proc S{lockvar} (Call (MailFSMergedOp__Lock u)) = do
  debugmsgs ["Lock ", u]
  lck <- withFd (dirPath u "mail") ReadOnly Nothing (\fd -> lockFd fd Exclusive Block)
  putMVar lockvar lck
  return $ unsafeCoerce ()

run_proc S{lockvar} (Call (MailFSMergedOp__Unlock u)) = do
  debugmsgs ["Unlock ", u]
  lck <- takeMVar lockvar
  unlock lck
  return $ unsafeCoerce ()

run_proc _ (Call (MailFSMergedOp__Exists u)) = {-# SCC "Exists" #-} do
  debugmsgs ["Exists ", u]
  ok <- fileExist (userPath u)
  if ok then do
    return $ unsafeCoerce (Horizontal.Present u)
  else do
    return $ unsafeCoerce Horizontal.Missing
