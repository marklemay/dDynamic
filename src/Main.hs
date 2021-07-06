module Main where

import Repl

main :: IO ()
main = do
  flushStr "Dtest repl!"
  putStrLn ""
  repl
