module POP3
  ( POP3Server(..)
  , pop3Listen
  , pop3Accept
  , pop3ProcessAuth
  , pop3Authenticate
  , pop3RespondAuth
  , pop3ProcessCommands
  , pop3GetRequest
  , pop3RespondStat
  , pop3RespondList
  , pop3RespondRetr
  , pop3RespondDelete
  ) where

-- Haskell libraries

import Control.Monad
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC8
import Data.Char
import Network
import System.IO

-- Extracted code

import MailServerAPI

-- Our libraries

import Support

-- POP3 implementation

data POP3Server =
  POP3Server Socket

pop3Listen :: Int -> IO POP3Server
pop3Listen portnum = do
  sock <- listenOn (PortNumber $ fromIntegral portnum)
  return $ POP3Server sock

pop3Accept :: POP3Server -> IO POP3Conn
pop3Accept (POP3Server sock) = do
  (conn, _, _) <- accept sock
  hSetBuffering conn LineBuffering
  pop3RespondOK conn
  return $ POP3Conn conn

hPutStrs :: Handle -> [BS.ByteString] -> IO ()
hPutStrs h = BS.hPutStr h . BS.concat

intToStr :: Integer -> BS.ByteString
intToStr = BSC8.pack . show

pop3Respond :: Handle -> Bool -> BS.ByteString -> IO ()
pop3Respond h True text =
  hPutStrs h $ ["+OK ", text, "\r\n"]
pop3Respond h False text =
  hPutStrs h $ ["-ERR ", text, "\r\n"]

pop3RespondOK :: Handle -> IO ()
pop3RespondOK h =
  pop3Respond h True ""

pop3ProcessAuth :: Handle -> IO (Maybe String)
pop3ProcessAuth h = do
  line <- hGetLine h
  let cmdparts = words line
  case cmdparts of
    cmd : rest ->
      case (map toUpper cmd) : rest of
        ["USER", u] -> do
          return $ Just u
        "CAPA" : _ -> do
          pop3RespondOK h
          hPutStr h ".\r\n"
          pop3ProcessAuth h
        "QUIT" : _ -> do
          pop3RespondOK h
          hClose h
          return Nothing
        _ -> do
          pop3Respond h False "unrecognized command"
          pop3ProcessAuth h
    _ -> do
      pop3Respond h False "unrecognized command"
      pop3ProcessAuth h

pop3Authenticate :: POP3Conn -> IO (Maybe String)
pop3Authenticate (POP3Conn h) = do
  pop3ProcessAuth h

pop3RespondAuth :: POP3Conn -> Bool -> IO ()
pop3RespondAuth (POP3Conn h) True = do
  pop3RespondOK h
pop3RespondAuth (POP3Conn h) False = do
  pop3Respond h False "unknown user"
  hClose h

pop3ProcessCommands :: Handle -> IO MailServerOp__Coq_pop3req
pop3ProcessCommands h = do
  line <- hGetLine h
  let cmdparts = words line
  case cmdparts of
    cmd : rest ->
      case (map toUpper cmd) : rest of
        "APOP" : _ -> do
          pop3RespondOK h
          pop3ProcessCommands h
        "USER" : _ -> do
          pop3RespondOK h
          pop3ProcessCommands h
        "PASS" : _ -> do
          pop3RespondOK h
          pop3ProcessCommands h
        "CAPA" : _ -> do
          pop3RespondOK h
          hPutStr h ".\r\n"
          pop3ProcessCommands h
        "STAT" : _ -> do
          return $ MailServerOp__POP3Stat
        "LIST" : _ -> do
          return $ MailServerOp__POP3List
        ["RETR", id] -> do
          return $ MailServerOp__POP3Retr $ read id - 1
        ["DELE", id] -> do
          return $ MailServerOp__POP3Delete $ read id - 1
        "QUIT" : _ -> do
          pop3RespondOK h
          hClose h
          return MailServerOp__POP3Closed
        _ -> do
          pop3Respond h False "unrecognized command"
          pop3ProcessCommands h
    _ -> do
      pop3Respond h False "unrecognized command"
      pop3ProcessCommands h

pop3GetRequest :: POP3Conn -> IO MailServerOp__Coq_pop3req
pop3GetRequest (POP3Conn h) = do
  pop3ProcessCommands h

pop3RespondStat :: POP3Conn -> Integer -> Integer -> IO ()
pop3RespondStat (POP3Conn h) count size = do
  pop3Respond h True $ BS.concat [intToStr count, " ", intToStr size]

pop3RespondList :: POP3Conn -> [Integer] -> IO ()
pop3RespondList (POP3Conn h) msglens = do
  pop3RespondOK h
  foldM (\idx msglen -> do
    BS.hPutStr h $ BS.concat [intToStr idx, " ", intToStr msglen, "\r\n"]
    return $ idx + 1) 1 msglens
  BS.hPutStr h ".\r\n"

pop3RespondRetr :: POP3Conn -> BS.ByteString -> IO ()
pop3RespondRetr (POP3Conn h) body = do
  pop3RespondOK h
  BS.hPutStr h body
  BS.hPutStr h ".\r\n"

pop3RespondDelete :: POP3Conn -> IO ()
pop3RespondDelete (POP3Conn h) = do
  pop3RespondOK h
