module Errors where
import Ast
import Prelude hiding (lookup)
import Data.Map

-- errors

baseErrorMessage :: String
baseErrorMessage = "Interpretation error: "

baseInternalErrorMessage :: String
baseInternalErrorMessage = "Internal interpretation error: "

-- helpers for erros
showValueType :: GoValue -> String
showValueType (VInt _)    = "int"
showValueType (VString _) = "string"
showValueType (VBool _)   = "bool"
showValueType (VArray x sizes)  = case lookup 0 x of
  (Just e) -> "array of " ++ showValueType e
  Nothing  -> undefined
showValueType _ = undefined

showType :: GoType -> String
showType TInt    = "int"
showType TString = "string"
showType TBool   = "bool"
showType (TArray x t)  = "array of " ++ showType t
showType _ = undefined

errorUnexpectedType :: GoValue -> String -> String -> String
errorUnexpectedType v act t = 
    baseErrorMessage ++ "unexpected type for " ++ act ++
    "\nexpected type: " ++ t ++
    "\nactual type: " ++ showValueType v

errorUnexpectedTypes :: GoValue -> GoValue -> BinOp -> String -> String -> String
errorUnexpectedTypes v1 v2 op t1 t2 = 
    baseErrorMessage ++ "unexpected type for " ++ show op ++
    "\nexpected types: " ++ t1 ++ " " ++ t2 ++
    "\nactual types: " ++ showValueType v1 ++ " " ++ showValueType v2

errorVarNotInScope :: Id -> String
errorVarNotInScope id = "Var " ++ id ++ " not in scope"

errorAssigmnetsType :: Id -> GoValue -> GoType -> String
errorAssigmnetsType id v t = baseErrorMessage ++ "x = expr, type x = " ++ showValueType v
  ++ "; type expr = " ++ showType t

errorRedeclarationConst :: Id -> String
errorRedeclarationConst id = "redeclaration const " ++ id

errorNotBoolInIf :: GoValue -> String
errorNotBoolInIf v = baseErrorMessage ++ "not bool type in if: " ++ showValueType v

errorAssignToConst :: Id -> String
errorAssignToConst id = baseErrorMessage ++ "assign to const " ++ id

errorNotBoolExprInFor :: String
errorNotBoolExprInFor = baseErrorMessage ++ "not bool expression in for"

errorIndexOutOfRange :: Int ->  String
errorIndexOutOfRange i = baseErrorMessage ++ "index out of range: " ++ show i

internalErrorEmptyFrameStack :: String
internalErrorEmptyFrameStack = baseInternalErrorMessage ++ "empty frame stack"

unexpectedInternalError :: a
unexpectedInternalError = error $ baseInternalErrorMessage ++ "unexpexted error"