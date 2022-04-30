module Interpreter where
import Prelude hiding (lookup)
import Ast
import Control.Monad.State.Lazy (gets, evalState, MonadState(get, put), StateT, lift, runStateT, forM)
import Control.Monad.Except
import Data.Map (Map, lookup, empty, insert)
import Runtime
import BaseFunc
import Errors
import Types

opTypeCheck :: BinOp -> GoValue -> GoValue -> Runtime ()
opTypeCheck op v1 v2
  | op `elem` [Minus, Mul, Div, Mod, Gr, Le, Gre, Leq] = do
    let isIntV1 = typeCheckVT v1 TInt
    let isIntV2 = typeCheckVT v2 TInt
    if isIntV1 && isIntV2 then 
      return () 
    else 
      throwError $ exceptionUnexpectedTypes v1 v2 op "int" "int"
  | op `elem` [And, Or] = do
    let isBoolV1 = typeCheckVT v1 TBool
    let isBoolV2 = typeCheckVT v2 TBool
    if isBoolV1 && isBoolV2 then 
      return () 
    else 
      throwError $ exceptionUnexpectedTypes v1 v2 op "bool" "bool"
  | op `elem` [Eq, Neq] = do
    if typeCheckVV v1 v2 then 
      return () 
    else 
      throwError $ exceptionUnexpectedTypes v1 v2 op "t" "t"
  | op == Add = do
    let isIntV1 = typeCheckVT v1 TInt
    let isIntV2 = typeCheckVT v2 TInt
    let isStringV1 = typeCheckVT v1 TString
    let isStringV2 = typeCheckVT v2 TString
    if isIntV1 && isIntV2 || isStringV1 && isStringV2 then 
      return () 
    else 
      throwError $ exceptionUnexpectedTypes v1 v2 op "int | string" "int | string"
  | otherwise = undefined

checkIfSt :: GoExpr -> Runtime () -> Runtime () -> Runtime ()
checkIfSt e tr fl = do
  res <- evalExpr e
  case res of
    (VBool True) -> tr
    (VBool False) -> fl
    _ -> throwError $ exceptionNotBoolInIf res

evalBinOp :: BinOp -> GoValue -> GoValue -> GoValue
evalBinOp op v1 v2 = case op of
-- int
  Add   -> v1   +   v2 -- and string
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
  opTypeCheck op v1 v2
  return $ evalBinOp op v1 v2

evalExpr (GoUnOp op e) = do
  v <- evalExpr e
  return $ evalUnOp op v

evalExpr (Var idr)  = getVarValue idr

evalExpr (Val v)   = return v

evalExpr EmptyCondition = return $ VBool True

evalExpr (GetByInd arr ind) = do -- fix for multid array
  varr <- evalExpr arr
  vind <- evalExpr ind
  case (varr, vind) of
    (VArray lst _, VInt i) -> safeInd lst i
    _                      -> unexpectedInternalError
  where
    safeInd :: Map Int GoValue -> Int -> Runtime GoValue
    safeInd lst i = case lookup i lst of
      (Just v) -> return v
      Nothing  -> throwError $ exceptionIndexOutOfRange i

evalExpr (FuncCall idr arge) = do
  f <- getVarValue idr
  case f of
    (VFunc args _ body) -> do
      argv <- forM arge evalExpr
      pushFrame
      pushScope
      putArgs argv args
      evalStatement body
      returnVal <$> popFrame
    _                 -> throwError $ exceptionCallNotFunc idr

evalExpr _ = undefined


evalStatement :: GoStatement -> Runtime ()

evalStatement (VarDecl idr t e) = do
  res <- evalExpr e
  if not (typeCheckVT res t)  then
    throwError $ exceptionAssigmnetsType idr res t
  else
    putVar idr (t, res)

evalStatement (ConstDecl idr t e) = do
  res <- evalExpr e
  if not (typeCheckVT res t)  then
    throwError $ exceptionAssigmnetsType idr res t
  else
    putConst idr (t, res)

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
  lift $ lift $ putStrLn $ toPrint res

evalStatement (If e s) = do
  pushScope
  checkIfSt e (evalStatement s) (return ())
  popScope

evalStatement(IfElse e s1 s2) = do
  pushScope
  checkIfSt e (evalStatement s1) (evalStatement s2)
  popScope

evalStatement (Assign idr e) = do
  res <- evalExpr e
  t   <- getVarType idr
  s   <- isConst idr
  if s then
    throwError $ exceptionAssignToConst idr
  else
    if not (typeCheckVT res t) then
      throwError $ exceptionAssigmnetsType idr res t
    else
      changeVar idr res

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

evalStatement (FuncDecl idr args rt body) = do
  case body of 
    (Block _) -> do
      let v = VFunc args rt body
      let t = TFunc args rt
      putVar idr (t, v)
    _         -> unexpectedInternalError -- тут точно должен поймать парсер


evalStatement (SetByInd idr ind e) = do
  arr <- evalExpr (Var idr)
  vind <- evalExpr ind
  v   <- evalExpr e
  if typeCheckVT v (getArrayElemType arr) then 
    throwError "[type] doesnt subs" -- fix me
  else
    case (arr, vind) of
      (VArray arr sizes, VInt i) -> do
        let res = insert i v arr in evalStatement (Assign idr (Val (VArray res sizes)))
      _                        -> throwError "[arr name] doesnt array" -- fix me

evalStatement (Jump (Return e)) = do
  v <- evalExpr e
  putReturnValue v
  putJumpSt $ Just $ Return e

evalStatement (Jump s) = putJumpSt $ Just s

evalStatement (Expr e) = do
  evalExpr e
  return ()

evalGoProgram :: GoProgram -> Runtime ()
evalGoProgram (GoProgram (x:xs)) = do
  evalStatement x
  evalGoProgram $ GoProgram xs
evalGoProgram (GoProgram []) = return ()


exec :: GoProgram -> IO (Either String GoValue, GoRuntime)
exec p = runStateT (runExceptT  (evalGoProgram p >> evalExpr goMain)) emptyGoRuntime
  where
    goMain = FuncCall "main" []