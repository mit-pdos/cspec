{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE RecordWildCards #-}
module Main where

import Control.Monad (when, forM_)
import Data.Semigroup ((<>))
import Network.NBD (runServer, initServer, ServerOptions (..))
import Options.Applicative
import System.Directory
import System.IO

data InitOptions = InitOptions
  { defaultSizeKB :: Int
  , initDiskPath :: FilePath
  , initBadSector :: Integer }

data Options = Start ServerOptions
             | Init InitOptions

parseDiskPath :: Parser FilePath
parseDiskPath = argument str (metavar "FILE0") <|> pure ("disk.img")

parseBadSector :: Parser Integer
parseBadSector = argument auto (metavar "BADSECTOR") <|> pure 1

serverOptions :: Parser ServerOptions
serverOptions = do
  diskPath <- parseDiskPath
  diskBadSector <- parseBadSector
  logCommands <- switch (long "debug"
                        <> short 'd'
                        <> help "log each operation received")
  pure ServerOptions {..}

initOptions :: Parser InitOptions
initOptions = do
  defaultSizeKB <- option auto
    ( long "size"
      <> help "size to initialize disk files to if they do not exist"
      <> showDefault
      <> value (100*1024)
      <> metavar "KB" )
  initDiskPath <- parseDiskPath
  initBadSector <- parseBadSector
  pure InitOptions {..}

diskDefaultMessage :: String
diskDefaultMessage = "disks default to disk0.img and disk1.img if not provided"

options :: Parser Options
options = hsubparser
          ( command "start" (info (Start <$> serverOptions)
                             (progDesc "start server"
                             <> footer diskDefaultMessage))
            <> command "init" (info (Init <$> initOptions)
                               (progDesc "initialize replicated disks"
                               <> footer diskDefaultMessage))
          )

main :: IO ()
main = execParser opts >>= run
  where
    opts = info (options <**> helper)
      (fullDesc
       <> progDesc "an nbd server that replicates over two disks; COMMAND is either init or start"
       <> header "replicate-nbd - replicating network block device"
       )

run :: Options -> IO ()
run (Start opts) = runServer opts
run (Init opts) = runInit opts

runInit :: InitOptions -> IO ()
runInit InitOptions
  { defaultSizeKB=size,
    initDiskPath=fn,
    initBadSector=bs } = do
  exists <- doesFileExist fn
  when (not exists) $
    withFile fn WriteMode $ \h ->
      hSetFileSize h (fromIntegral $ size * 1024)
  initServer fn bs
