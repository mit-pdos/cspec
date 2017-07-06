module Main where

import Variables.Env
import StatDbCli

main :: IO ()
main = do
  e <- newEnv
  runVars e cli
