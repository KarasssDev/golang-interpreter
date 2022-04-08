module Interpreter where
import Prelude hiding (lookup)
import Ast
import Control.Monad.State (gets, evalState, MonadState(get, put), State )
import Data.Map (Map, lookup, empty, insert)
import Runtime
import BaseFunc
import Errors



getValue :: Runtime GoValue  -> GoValue
getValue r = evalState r emptyGoRuntime

evalExpr :: GoExpr -> GoRuntime -> GoValue
-- int
evalExpr (Add   e1 e2) r = evalExpr e1 r   +   evalExpr e2 r
evalExpr (Minus e1 e2) r = evalExpr e1 r   -   evalExpr e2 r
evalExpr (Mul   e1 e2) r = evalExpr e1 r   *   evalExpr e2 r
evalExpr (Div   e1 e2) r = evalExpr e1 r `div` evalExpr e2 r
evalExpr (Mod   e1 e2) r = evalExpr e1 r `mod` evalExpr e2 r
evalExpr (UnMinus e)   r = - evalExpr e r
-- bool 
evalExpr (And e1 e2) r = evalExpr e1 r `goAnd` evalExpr e2 r
evalExpr (Or  e1 e2) r = evalExpr e1 r `goOr`  evalExpr e2 r
evalExpr (Not e)     r = goNot $ evalExpr e r
-- comparsions
evalExpr (Eq  e1 e2) r = VBool $ evalExpr e1 r == evalExpr e2 r
evalExpr (Gr  e1 e2) r = VBool $ evalExpr e1 r >  evalExpr e2 r
evalExpr (Le  e1 e2) r = VBool $ evalExpr e1 r <  evalExpr e2 r
evalExpr (Gre e1 e2) r = VBool $ evalExpr e1 r >= evalExpr e2 r
evalExpr (Leq e1 e2) r = VBool $ evalExpr e1 r <= evalExpr e2 r
evalExpr (Neq e1 e2) r = VBool $ evalExpr e1 r /= evalExpr e2 r
-- other
evalExpr (Var id) r = getOrError id r
evalExpr (Val x) r = x
evalExpr _ _ = undefined


evalStatement :: GoStatement -> Runtime ()

evalStatement (VarDecl id t e) = do
  r <- get
  let res = evalExpr e r
  if showValueType res /= showType t then
    errorAssigmnetsType id res t
  else
    putVar id (t, res)

evalStatement (ConstDecl id t e) = do
  r <- get
  let res = evalExpr e r
  if showValueType res /= showType t then
    errorAssigmnetsType id res t
  else
    putConst id (t, res)

evalStatement (Block b) = case b of
  [] -> error "empty block"
  [x] -> evalStatement x
  x:xs -> do
     evalStatement x
     evalStatement (Block xs)

evalStatement (Print e) = do
  r <- get
  goPrint $ evalExpr e r

evalStatement (If e s) = do
  r <- get 
  let res = evalExpr e r
  case res of 
    (VBool True) -> evalStatement s
    (VBool False) -> return ()
    _ -> errorNotBoolInIf res 

evalStatement _ = undefined
