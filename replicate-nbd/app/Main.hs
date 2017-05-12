module Main where

import Control.Monad (unless, forM_)
import Network.NBD (runServer)
import System.Directory
import System.IO

-- TODO: need to support argument/option parsing for file names
fn0 :: FilePath
fn0 = "disk0.img"

fn1 :: FilePath
fn1 = "disk1.img"

-- if creating empty disk0.img, disk1.img, size to set in bytes
size :: Integer
size = 100*1024*1024

main :: IO ()
main = do
  exists0 <- doesFileExist fn0
  exists1 <- doesFileExist fn1
  unless (exists0 && exists1) $
    forM_ [fn0, fn1] $ \p ->
      withFile p WriteMode $ \h ->
        hSetFileSize h size
  runServer fn0 fn1
