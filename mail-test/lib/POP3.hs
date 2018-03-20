module POP3 where

import Control.Monad
import Network
import System.IO

data POP3Server =
  POP3Server Socket

data POP3Conn =
  POP3Conn Handle

data POP3Command =
    POP3Delete (Integer, Integer)
  | POP3Closed

pop3Listen :: Int -> IO POP3Server
pop3Listen portnum = do
  sock <- listenOn (PortNumber $ fromIntegral portnum)
  return $ POP3Server sock

pop3Accept :: POP3Server -> IO POP3Conn
pop3Accept (POP3Server sock) = do
  (conn, _, _) <- accept sock
  hSetBuffering conn NoBuffering
  return $ POP3Conn conn

pop3Respond :: Handle -> Bool -> String -> IO ()
pop3Respond h True text =
  hPutStrLn h $ "+OK " ++ text
pop3Respond h False text =
  hPutStrLn h $ "-ERR " ++ text

pop3RespondOK :: Handle -> IO ()
pop3RespondOK h =
  pop3Respond h True ""

pop3ProcessCommands :: Handle -> [((Integer, Integer), String)] -> IO POP3Command
pop3ProcessCommands h msgs = do
  line <- hGetLine h
  let cmd = words line
  case cmd of
    "APOP" : _ -> do
      pop3RespondOK h
      pop3ProcessCommands h msgs
    "USER" : _ -> do
      pop3RespondOK h
      pop3ProcessCommands h msgs
    "PASS" : _ -> do
      pop3RespondOK h
      pop3ProcessCommands h msgs
    "STAT" : _ -> do
      pop3Respond h True $ (show $ length msgs) ++ " " ++ (show $ sum $ map length $ map snd msgs)
      pop3ProcessCommands h msgs
    "LIST" : _ -> do
      pop3RespondOK h
      foldM (\idx msg -> do
        hPutStrLn h $ (show idx) ++ " " ++ (show $ length $ snd msg)
        return $ idx + 1) 1 msgs
      pop3ProcessCommands h msgs
    ["RETR", id] -> do
      pop3RespondOK h
      hPutStr h $ snd (msgs !! (read id - 1))
      hPutStrLn h "."
      pop3ProcessCommands h msgs
    ["DELE", id] -> do
      return $ POP3Delete $ fst (msgs !! (read id - 1))
    "QUIT" : _ -> do
      pop3RespondOK h
      hClose h
      return POP3Closed
    _ -> do
      pop3Respond h False "unrecognized command"
      pop3ProcessCommands h msgs

pop3GetRequest :: POP3Conn -> [((Integer, Integer), String)] -> IO POP3Command
pop3GetRequest (POP3Conn h) msgs = do
  pop3RespondOK h
  pop3ProcessCommands h msgs

pop3AckDelete :: POP3Conn -> IO ()
pop3AckDelete (POP3Conn h) = do
  return ()
