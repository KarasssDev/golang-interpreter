module Main where
import Ast
import Interpreter
import Control.Monad.State
import Data.Map

import Interpreter
import Ast
import Errors
import Runtime



e :: GoExpr 
e = Minus (Val (VInt 2)) (Var "x")

b :: GoStatement 
b = Block [VarDecl "x" TInt (Val (VInt 3)), 
           VarDecl "y" TInt (Minus (Val (VInt 2)) (Var "x")),
           Print (Var "y")
           ]



pprint :: [String] -> IO ()
pprint [] = undefined
pprint [x] = print x
pprint (x:xs) = do
    print x 
    pprint xs 

showVars :: GoStatement -> IO () 
showVars s = do
    let v = vars $ execState (evalStatement s) emptyGoRuntime
    pprint $ keys v

showVals :: GoStatement -> IO () 
showVals s = do
    let v = vars $ execState (evalStatement s) emptyGoRuntime
    pprint $ Prelude.map show (elems v)

exec :: GoStatement -> IO ()
exec s = do
    let r = execState (evalStatement s) emptyGoRuntime
    pprint $ toPrint r 

main :: IO ()
main = exec b
