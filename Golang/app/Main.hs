module Main where

import Control.Monad.State.Lazy
import Data.Map

import Interpreter
import Ast
import Errors
import Runtime hiding (head)
import Parser
import System.Environment

main = do
  args     <- getArgs
  let fileName = head args
  inp      <- readFile fileName
  let prog = cleanFile inp
  case (goParse prog) of
    Left err -> print err
    Right p  -> do
      exec p
      return ()

-- main = do
--   s <- getLine
--   p s