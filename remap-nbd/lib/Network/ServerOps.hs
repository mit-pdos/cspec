module Network.ServerOps where

import NbdAPI
import Control.Monad.Reader (reader, liftIO)
import Control.Concurrent.MVar (takeMVar, putMVar)
import BadBlockDisk.Env

getRequestFromQueue :: TheProc Request
getRequestFromQueue = do
  m <- reader requests
  liftIO $ takeMVar m

sendResponseOnQueue :: Response -> TheProc ()
sendResponseOnQueue r = do
  m <- reader responses
  liftIO $ putMVar m r
