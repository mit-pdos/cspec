module Interpreter where

-- Haskell libraries
import Control.Concurrent
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

-- Extracted code
import ConcurProc
import MailFSPathAPI
import MailServer
import MailServerAPI

data State =
  S !(MVar Lock)

mkState :: IO State
mkState = do
  lockvar <- newEmptyMVar
  return $ S lockvar

verbose :: Bool
verbose = True

debugmsg :: String -> IO ()
debugmsg s =
  if verbose then do
    tid <- myThreadId
    putStrLn $ "[" ++ (show tid) ++ "] " ++ s
  else
    return ()

dirPath :: String -> String
dirPath dir = "/tmp/mailtest/" ++ dir

filePath :: String -> String -> String
filePath dir fn = (dirPath dir) ++ "/" ++ fn

run_proc :: State -> Coq_proc (MailFSPathAPI__Coq_xopT a) GHC.Prim.Any -> IO a
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

run_proc _ (Op MailFSPathAPI__GetTID) = do
  tid <- myThreadId
  -- Horrible hack: get the numeric TID by printing the ThreadId as a string,
  -- using [show], which returns something like "ThreadId 5", and then parse
  -- it back to Integer using [read].
  let (_, tidstr) = splitAt 9 (show tid) in do
    return $ unsafeCoerce (read tidstr :: Integer)

run_proc _ (Op MailFSPathAPI__Random) = do
  ts <- rdtsc
  return $ unsafeCoerce (fromIntegral ts :: Integer)

run_proc _ (Op (MailFSPathAPI__Ext (MailServerAPI__GetRequest))) = do
  debugmsg $ "GetRequest"
  rnd <- randomIO
  if (rnd :: Integer) `mod` 100 == 0 then
    return $ unsafeCoerce (MailServerAPI__ReqRead)
  else
    return $ unsafeCoerce (MailServerAPI__ReqDeliver "Test message")

run_proc _ (Op (MailFSPathAPI__Ext (MailServerAPI__Respond _))) = do
  debugmsg $ "Respond"
  return $ unsafeCoerce ()

run_proc _ (Op (MailFSPathAPI__CreateWrite (dir, fn) contents)) = do
  debugmsg $ "CreateWrite " ++ dir ++ "/" ++ fn ++ ", " ++ (show contents)
  writeFile (filePath dir fn) contents
  return $ unsafeCoerce ()

run_proc _ (Op (MailFSPathAPI__Link (srcdir, srcfn) (dstdir, dstfn))) = do
  debugmsg $ "Link " ++ srcdir ++ "/" ++ srcfn ++ " to " ++ dstdir ++ "/" ++ dstfn
  createLink (filePath srcdir srcfn) (filePath dstdir dstfn)
  return $ unsafeCoerce True

run_proc _ (Op (MailFSPathAPI__Unlink (dir, fn))) = do
  debugmsg $ "Unlink " ++ dir ++ "/" ++ (fn)
  removeLink (filePath dir fn)
  return $ unsafeCoerce ()

run_proc _ (Op (MailFSPathAPI__List dir)) = do
  debugmsg $ "List " ++ dir
  files <- listDirectory (dirPath dir)
  return $ unsafeCoerce files

run_proc _ (Op (MailFSPathAPI__Read (dir, fn))) = do
  debugmsg $ "Read " ++ dir ++ "/" ++ fn
  catch (do
           h <- openFile (filePath dir fn) ReadMode
           contents <- hGetContents h
           hClose h
           return $ unsafeCoerce (Just contents))
        (\e -> case e of
               _ | isDoesNotExistError e -> do
                 debugmsg "Reading a non-existant file"
                 return $ unsafeCoerce Nothing
               _ -> do
                 debugmsg "Unknown exception on read"
                 return $ unsafeCoerce Nothing)

run_proc (S lockvar) (Op (MailFSPathAPI__Lock)) = do
  debugmsg $ "Lock"
  mboxfd <- openFd (dirPath "mail") ReadOnly Nothing defaultFileFlags
  lck <- lockFd mboxfd Exclusive Block
  closeFd mboxfd
  putMVar lockvar lck
  return $ unsafeCoerce ()

run_proc (S lockvar) (Op (MailFSPathAPI__Unlock)) = do
  debugmsg $ "Unlock"
  lck <- takeMVar lockvar
  unlock lck
  return $ unsafeCoerce ()
