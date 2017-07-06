module CLI.Stubs (getNewItem, reportMean) where

import Control.Monad.Reader (liftIO)
import Variables.Env
import System.IO

getNewItem :: TheProg Integer
getNewItem = do
  liftIO $ putStr "Enter a number to add: "
  liftIO $ hFlush stdout
  x <- liftIO $ getLine
  return $ read x

reportMean :: Maybe Integer -> TheProg ()
reportMean m = do
  liftIO $ putStrLn $ "Mean: " ++ (show m)
