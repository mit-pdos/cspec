module Network.ServerOps where

import NbdData
import Control.Monad.Reader (reader, liftIO)
import Control.Concurrent.MVar (takeMVar, putMVar)
import Replication.TwoDiskEnvironment

getRequestFromQueue :: TheProg Request
getRequestFromQueue = do
  m <- reader requests
  liftIO $ takeMVar m

sendResponseOnQueue :: Response -> TheProg ()
sendResponseOnQueue r = do
  m <- reader responses
  liftIO $ putMVar m r
