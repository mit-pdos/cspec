module CLI.Stubs (getMail) where

import Control.Monad.Trans (liftIO)
import FS.State
import System.IO

getMail :: Proc String
getMail = do
  x <- liftIO $ do
    putStr "Enter text to send: "
    hFlush stdout
    getLine
  return $ read x

