{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE RecordWildCards #-}
module Main where

import Control.Monad (when, forM_)
import Data.Semigroup ((<>))
import Network.NBD (runServer, ServerOptions (..))
import Options.Applicative
import System.Directory
import System.IO

data Options = Options
  { defaultSizeKB :: Int
  , serverOpts :: ServerOptions }

serverOptions :: Parser ServerOptions
serverOptions = do
  diskPaths <- ((,)
                <$> argument str (metavar "FILE0")
                <*> argument str (metavar "FILE1"))
               <|> pure ("disk0.img", "disk1.img")
  logCommands <- switch (long "debug"
                        <> short 'd'
                        <> help "log each operation received")
  pure ServerOptions {..}

options :: Parser Options
options = do
  defaultSizeKB <- option auto
    ( long "size"
      <> help "size to initialize disk files to if they do not exist"
      <> showDefault
      <> value (100*1024)
      <> metavar "KB" )
  serverOpts <- serverOptions
  pure Options {..}

main :: IO ()
main = execParser opts >>= run
  where
    opts = info (options <**> helper)
      (fullDesc
       <> progDesc "start an nbd server that replicates over two disks"
       <> header "replicate-nbd - replicating network block device"
       <> footer "disks default to disk0.img and disk1.img if not provided")

run :: Options -> IO ()
run Options
  { defaultSizeKB=size,
    serverOpts=opts@ServerOptions
               { diskPaths=(fn0, fn1) } } = do
  exists0 <- doesFileExist fn0
  exists1 <- doesFileExist fn1
  when (not exists0 && not exists1) $
    forM_ [fn0, fn1] $ \p ->
      withFile p WriteMode $ \h ->
        hSetFileSize h (fromIntegral $ size * 1024)
  runServer opts
