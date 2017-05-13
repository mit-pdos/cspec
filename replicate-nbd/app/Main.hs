module Main where

import Control.Monad (unless, forM_)
import Data.Semigroup ((<>))
import Network.NBD (runServer)
import Options.Applicative
import System.Directory
import System.IO

data Options = Options
  { defaultSizeKB :: Int
  , disk0Path :: FilePath
  , disk1Path :: FilePath }

options :: Parser Options
options = Options
  <$> option auto
    ( long "size"
      <> help "size to initialize disk files to if they do not exist"
      <> showDefault
      <> value (100*1024)
      <> metavar "KB" )
  <*> strOption
    ( long "disk0"
      <> metavar "FILE"
      <> help "file to use as disk0"
      <> showDefault
      <> value "disk0.img" )
  <*> strOption
    ( long "disk1"
      <> metavar "FILE"
      <> help "file to use as disk1"
      <> showDefault
      <> value "disk1.img" )

main :: IO ()
main = execParser opts >>= run
  where
    opts = info (options <**> helper)
      (fullDesc
       <> progDesc "start an nbd server that replicates over two disks"
       <> header "replicate-nbd - replicating network block device")

run :: Options -> IO ()
run Options {defaultSizeKB=size, disk0Path=fn0, disk1Path=fn1} = do
  exists0 <- doesFileExist fn0
  exists1 <- doesFileExist fn1
  unless (exists0 && exists1) $
    forM_ [fn0, fn1] $ \p ->
      withFile p WriteMode $ \h ->
        hSetFileSize h (fromIntegral $ size * 1024)
  runServer fn0 fn1
