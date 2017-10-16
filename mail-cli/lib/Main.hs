{-# OPTIONS_GHC -F -pgmF ./fiximports.py #-}
module Main where

import FS.State
import MailCli

main :: IO ()
main = runFS cli
