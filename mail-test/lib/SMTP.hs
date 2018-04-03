module SMTP where

-- Loosely based on https://github.com/agrafix/haskell-smtp-server/blob/master/Smtp.hs

import Network
import System.IO
import Support

data SMTPServer =
  SMTPServer Socket

data Message =
  Message
    { mail_client :: [String]
    , mail_from :: [String]
    , mail_to :: String
    , mail_data :: String
    } deriving (Show, Eq)

smtpListen :: Int -> IO SMTPServer
smtpListen portnum = do
  sock <- listenOn (PortNumber $ fromIntegral portnum)
  return $ SMTPServer sock

smtpAccept :: SMTPServer -> IO SMTPConn
smtpAccept (SMTPServer sock) = do
  (conn, _, _) <- accept sock
  hSetBuffering conn LineBuffering
  return $ SMTPConn conn

smtpRespond :: Handle -> Int -> String -> IO ()
smtpRespond h code text =
  hPutStrLn h $ (show code) ++ " " ++ text

smtpRespondOK :: Handle -> IO ()
smtpRespondOK h =
  smtpRespond h 250 "OK"

smtpClose :: Handle -> IO ()
smtpClose h = do
  smtpRespond h 221 "closing"
  hClose h

process_to :: [String] -> String
process_to words =
  if length words >= 1 && (words !! 0) == "TO:"
  then filter (not . flip elem "<>") (words !! 1)
  else "still-unknown"

smtpProcessCommands :: Handle -> Message -> IO (Maybe Message)
smtpProcessCommands h msg = do
  line <- hGetLine h
  let cmd = words line
  case cmd of
    "HELO" : client -> do
      smtpRespondOK h
      smtpProcessCommands h $ msg { mail_client = client }
    "EHLO" : client -> do
      smtpRespondOK h
      smtpProcessCommands h $ msg { mail_client = client }
    "MAIL" : from -> do
      smtpRespondOK h
      smtpProcessCommands h $ msg { mail_from = from }
    "RCPT" : to -> do
      smtpRespondOK h
      -- putStrLn $ "to: " ++ process_to to
      smtpProcessCommands h $ msg { mail_to = process_to to }
    ["DATA"] -> do
      smtpRespond h 354 "proceed with data"
      smtpProcessData h msg
    ["QUIT"] -> do
      smtpClose h
      return Nothing
    _ -> do
      smtpRespond h 500 "unknown command"
      smtpClose h
      return Nothing

smtpProcessData :: Handle -> Message -> IO (Maybe Message)
smtpProcessData h msg = do
  line <- hGetLine h
  if line == ".\r" then
    return (Just msg)
  else do
    smtpProcessData h $ msg { mail_data = (mail_data msg) ++ line ++ "\n" }

smtpGetMessage :: SMTPConn -> IO (Maybe (String, String))
smtpGetMessage (SMTPConn h) = do
  smtpRespond h 220 "ready"
  maybemsg <- smtpProcessCommands h (Message [] [] "unknown" "")
  case maybemsg of
    Nothing -> return Nothing
    Just msg -> return $ Just (mail_to msg, mail_data msg)

smtpDone :: SMTPConn -> Bool -> IO ()
smtpDone (SMTPConn h) True = do
  smtpRespond h 250 "delivered"
  smtpClose h

smtpDone (SMTPConn h) False = do
  smtpRespond h 452 "could not deliver"
  smtpClose h
