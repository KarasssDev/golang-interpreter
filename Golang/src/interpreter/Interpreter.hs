module Interpreter where
import Prelude hiding (lookup)
import Ast
import Control.Monad.State (gets, evalState, MonadState(get, put), State )
import Data.Map (Map, lookup, empty, insert)
import Runtime
import BaseFunc
import Errors



evalBinOp :: BinOp -> GoValue -> GoValue -> GoValue 
evalBinOp op v1 v2 = case op of
-- int
  Add   -> v1   +   v2
  Minus -> v1   -   v2
  Mul   -> v1   *   v2
  Div   -> v1 `div` v2
  Mod   -> v1 `mod` v2
-- bool 
  And -> v1 `goAnd` v2
  Or  -> v1 `goOr`  v2
-- comparsions
  Eq  -> VBool $ v1 == v2
  Gr  -> VBool $ v1 >  v2
  Le  -> VBool $ v1 <  v2
  Gre -> VBool $ v1 >= v2
  Leq -> VBool $ v1 <= v2
  Neq -> VBool $ v1 /= v2

evalUnOp :: UnOp -> GoValue -> GoValue 
evalUnOp op v = case op of
  UnMinus -> -v
  Not     -> goNot v



evalExpr :: GoExpr -> Runtime GoValue

evalExpr (GoBinOp op e1 e2)  = do
  v1 <- evalExpr e1
  v2 <- evalExpr e2
  return $ evalBinOp op v1 v2

evalExpr (GoUnOp op e) = do
  v <- evalExpr e
  return $ evalUnOp op v


-- other
evalExpr (Var id) = getVarValue id
evalExpr (Val x)  = return x
evalExpr _  = undefined


evalStatement :: GoStatement -> Runtime ()

evalStatement (VarDecl id t e) = do
  res <- evalExpr e
  if showValueType res /= showType t then
    errorAssigmnetsType id res t
  else
    putVar id (t, res)

evalStatement (ConstDecl id t e) = do
  res <- evalExpr e
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
  res <- evalExpr e
  goPrint res

evalStatement (If e s) = do
  res <- evalExpr e
  case res of
    (VBool True) -> evalStatement s
    (VBool False) -> return ()
    _ -> errorNotBoolInIf res

evalStatement(IfElse e s1 s2) = do
  res <- evalExpr e
  case res of
    (VBool True)  -> evalStatement s1
    (VBool False) -> evalStatement s2
    _ -> errorNotBoolInIf res

evalStatement (Assign id e) = do
  res <- evalExpr e
  t   <- getVarType id
  s   <- isConst id
  if s then
    errorAssignToConst id
  else
    if showValueType res /= showType t then
      errorAssigmnetsType id res t
    else
      putVar id (t, res)

evalStatement _ = undefined
