module Main where


import Interpreter ( exec )
import Parser ( goParse, cleanFile )
import System.Environment ( getArgs )

main :: IO ()
main = do
  args     <- getArgs
  case args of 
    fileName:_ -> do
      inp      <- readFile fileName
      let prog = cleanFile inp
      case goParse prog of
        Left err -> print err
        Right p  -> do
          (res, _) <- exec p
          case res of 
            (Left err) -> print err
            (Right _)  -> return ()
    [] -> print "Expected filename in args"
