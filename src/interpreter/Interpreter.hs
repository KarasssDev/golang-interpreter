module Interpreter where
import Prelude hiding (lookup)
import Ast
import Control.Monad.State.Lazy (gets, evalState, MonadState(get, put), StateT, lift, runStateT, forM)
import Data.Map (Map, lookup, empty, insert)
import Runtime
import BaseFunc
import Errors


typeCheck :: GoValue -> GoType -> () -> ()
typeCheck v t f = if eq v t then () else f
  where 
-- fix me (arrays, funcs and channels)
    eq (VInt x) TInt = True
    eq (VString s) TString = True
    eq (VBool b) TBool = True
    eq _ _ = True

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

evalExpr (Var id)  = getVarValue id

evalExpr (Val v)   = return v

evalExpr EmptyCondition = return $ VBool True 

evalExpr (GetByInd arr ind) = do
  varr <- evalExpr arr
  vind <- evalExpr ind
  case (varr, vind) of 
    ((VArray lst), (VInt i)) -> return $ safeInd lst i
    _                        -> undefined -- видимо должен поймать парсер
  where
    safeInd lst i = case (lookup i lst) of
      (Just v) -> v
      Nothing  -> errorIndexOutOfRange i

evalExpr (FuncCall id arge) = do -- add check (f == func)
  f <- getVarValue id
  case f of 
    (VFunc args body) -> do
      argv <- forM arge evalExpr
      pushFrame
      pushScope
      putArgs argv args
      evalStatement body
      fr <- popFrame
      return $ returnVal fr
    _                 -> error "fix me3" 

evalExpr _ = undefined


evalStatement :: GoStatement -> Runtime ()

evalStatement (VarDecl id t e) = do
  res <- evalExpr e
  return $ typeCheck res t (errorAssigmnetsType id res t)
  putVar id (t, res)

evalStatement (ConstDecl id t e) = do
  res <- evalExpr e
  return $ typeCheck res t (errorAssigmnetsType id res t)
  putConst id (t, res)

evalStatement (Block b) = do 
  j <- getJumpSt
  case j of
    Just s  -> return ()
    Nothing -> case b of
      [] -> return ()
      x:xs ->  case x of 
        (Jump s) -> do
          evalStatement x
          return ()
        _        -> do 
          evalStatement x
          evalStatement (Block xs)


evalStatement (Print e) = do
  res <- evalExpr e
  lift $ print res

evalStatement (If e s) = do
  pushScope
  checkIfSt e (evalStatement s) (return ())
  popScope

evalStatement(IfElse e s1 s2) = do
  pushScope
  checkIfSt e (evalStatement s1) (evalStatement s2)
  popScope

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
      changeVar id res

evalStatement EmptyStatement = return ()

evalStatement (For init cont di act) = do
  pushScope
  evalStatement init
  for cont di act
  popScope
  where 
    for cont di act = do
      checkIfSt cont (evalStatement act) (return ())
      evalStatement di
      j <- getJumpSt 
      case j of 
        Just x  -> case x of
          Break      -> do
            putJumpSt Nothing 
            return ()
          Continue   -> do
            putJumpSt Nothing
            checkIfSt cont (for cont di act) (return ())
          (Return e) -> do
            return ()
        Nothing -> checkIfSt cont (for cont di act) (return ())

evalStatement (FuncDecl id args rt body) = do -- add check body == Block
  let v = VFunc args body
  let t = TFunc args rt
  putVar id (t, v)


evalStatement (SetByInd id ind e) = do
  arr <- evalExpr (Var id)
  vind <- evalExpr ind
  v   <- evalExpr e
  -- fix me (add assign type check)
  case (arr, vind) of
    ((VArray arr), (VInt i)) -> do
      let res = (insert i v arr) in evalStatement (Assign id (Val (VArray res)))
    _                        -> undefined -- видимо должен поймать парсер

evalStatement (Jump (Return e)) = do
  v <- evalExpr e
  putReturnValue v
  putJumpSt $ Just $ Return e

evalStatement (Jump s) = putJumpSt $ Just s

evalStatement (Expr e) = do
  evalExpr e
  return ()

evalStatement _ = undefined


evalGoProgram :: GoProgram -> Runtime ()
evalGoProgram (GoProgram (x:xs)) = do
  evalStatement x
  evalGoProgram $ GoProgram xs
evalGoProgram (GoProgram []) = return ()

exec :: GoProgram -> IO (GoValue, GoRuntime)
exec p = runStateT (evalGoProgram p >> evalExpr goMain) emptyGoRuntime
  where
    goMain = FuncCall "main" []