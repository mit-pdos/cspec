module POP3 where

-- Haskell libraries

import Control.Monad
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
  hSetBuffering conn NoBuffering
  pop3RespondOK conn
  return $ POP3Conn conn

pop3Respond :: Handle -> Bool -> String -> IO ()
pop3Respond h True text =
  hPutStr h $ "+OK " ++ text ++ "\r\n"
pop3Respond h False text =
  hPutStr h $ "-ERR " ++ text ++ "\r\n"

pop3RespondOK :: Handle -> IO ()
pop3RespondOK h =
  pop3Respond h True ""

pop3ProcessCommands :: Handle -> IO MailServerAPI__Coq_pop3req
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
          return $ MailServerAPI__POP3Stat
        "LIST" : _ -> do
          return $ MailServerAPI__POP3List
        ["RETR", id] -> do
          return $ MailServerAPI__POP3Retr $ read id - 1
        ["DELE", id] -> do
          return $ MailServerAPI__POP3Delete $ read id - 1
        "QUIT" : _ -> do
          pop3RespondOK h
          hClose h
          return MailServerAPI__POP3Closed
        _ -> do
          pop3Respond h False "unrecognized command"
          pop3ProcessCommands h
    _ -> do
      pop3Respond h False "unrecognized command"
      pop3ProcessCommands h

pop3GetRequest :: POP3Conn -> IO MailServerAPI__Coq_pop3req
pop3GetRequest (POP3Conn h) = do
  pop3ProcessCommands h

pop3RespondStat :: POP3Conn -> Integer -> Integer -> IO ()
pop3RespondStat (POP3Conn h) count size = do
  pop3Respond h True $ (show count) ++ " " ++ (show size)

pop3RespondList :: POP3Conn -> [Integer] -> IO ()
pop3RespondList (POP3Conn h) msglens = do
  pop3RespondOK h
  foldM (\idx msglen -> do
    hPutStr h $ (show idx) ++ " " ++ (show msglen) ++ "\r\n"
    return $ idx + 1) 1 msglens
  hPutStr h ".\r\n"

pop3RespondRetr :: POP3Conn -> String -> IO ()
pop3RespondRetr (POP3Conn h) body = do
  pop3RespondOK h
  hPutStr h body
  hPutStr h ".\r\n"

pop3RespondDelete :: POP3Conn -> IO ()
pop3RespondDelete (POP3Conn h) = do
  pop3RespondOK h
