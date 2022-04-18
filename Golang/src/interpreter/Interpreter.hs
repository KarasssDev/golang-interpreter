module Interpreter where
import Prelude hiding (lookup)
import Ast
import Control.Monad.State.Lazy (gets, evalState, MonadState(get, put), StateT, lift )
import Data.Map (Map, lookup, empty, insert)
import Runtime
import BaseFunc
import Errors

-- (!?) :: [a] -> Int -> Maybe a
-- []     !? i = Nothing
-- (x:xs) !? i = if i == 0 then (Just x) else (xs !? (i - 1))

-- setInd :: a -> Int -> [a] -> Maybe [a]
-- setInd v i lst = helper v i lst []
--   where 
--     helper v i []     r = if i == -1 then (Just (reverse r)) else Nothing
--     helper v 0 (x:xs) r = helper v (-1)    xs (v:r)
--     helper v i (x:xs) r = helper v (i - 1) xs (x:r)


checkIfSt :: GoExpr -> Runtime () -> Runtime () -> Runtime ()
checkIfSt e tr fl = do
  res <- evalExpr e
  case res of
    (VBool True) -> tr
    (VBool False) -> fl
    _ -> errorNotBoolInIf res

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
evalExpr (Var id)  = getVarValue id
evalExpr (Val x)   = return x
evalExpr EmptyCondition = return $ VBool True 
evalExpr (GetByInd arr ind) = do
  varr <- evalExpr arr
  vind <- evalExpr ind
  case (varr, vind) of 
    ((VArray lst), (VInt i)) -> return $ safeInd lst i
    _                        -> error $ "fix me"
  where
    safeInd lst i = case (lookup i lst) of
      (Just v) -> v
      Nothing  -> error $ "fix me"

evalExpr _ = undefined


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

evalStatement (Block b) = do 
  j <- getJumpSt
  case j of
    Just s  -> return ()
    Nothing -> case b of
      [] -> return ()
      x:xs ->  case x of 
        (Jump s) -> do
          putJumpSt $ Just s
          return ()
        _        -> do 
          evalStatement x
          evalStatement (Block xs)


evalStatement (Print e) = do
  res <- evalExpr e
  lift $ print $ show res

evalStatement (If e s) = checkIfSt e (evalStatement s) (return ())

evalStatement(IfElse e s1 s2) = checkIfSt e (evalStatement s1) (evalStatement s2)

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

evalStatement EmptyStatement = return ()

evalStatement (For init cont di act) = do
  evalStatement init
  for cont di act
  where 
    for cont di act = do
      checkIfSt cont (evalStatement act) (return ())
      evalStatement di
      j <- getJumpSt 
      case j of 
        Just x  -> case x of
          Break    -> do
            putJumpSt Nothing 
            return ()
          Continue -> do
            putJumpSt Nothing
            checkIfSt cont (for cont di act) (return ())
        Nothing -> checkIfSt cont (for cont di act) (return ())
      

evalStatement (SetByInd id arr ind v) = do
  varr <- evalExpr arr
  vind <- evalExpr ind
  vv   <- evalExpr v
  -- fix me (add assign type check)
  case (varr, vind) of
    ((VArray arr), (VInt i)) -> let res = (insert i vv arr) in evalStatement (Assign id (Val (VArray res)))
    _                        -> error $ "fix me"


evalStatement (Jump Continue) = putJumpSt $ Just Continue
evalStatement (Jump Break)    = putJumpSt $ Just Break 

evalStatement _ = undefined
