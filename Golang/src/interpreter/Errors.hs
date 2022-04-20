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
showValueType (VArray x)  = case (lookup 0 x) of 
  (Just e) -> "array of " ++ showValueType e
  Nothing  -> undefined 


showType :: GoType -> String
showType TInt    = "int"
showType TString = "string"
showType TBool   = "bool"
showType (TArray x t)  = "array of " ++ showType t
showType _ = undefined

errorUnexpectedType :: GoValue -> String -> String -> a
errorUnexpectedType v act t = error $
    baseErrorMessage ++ "unexpected type for " ++ act ++
    "\nexpected type: " ++ t ++
    "\nactual type: " ++ showValueType v

errorUnexpectedTypes :: GoValue -> GoValue -> String -> String -> String -> a
errorUnexpectedTypes v1 v2 act t1 t2 = error $
    baseErrorMessage ++ "unexpected type for " ++ act ++
    "\nexpected types: " ++ t1 ++ " " ++ t2 ++
    "\nactual types: " ++ showValueType v1 ++ " " ++ showValueType v2

errorVarNotInScope :: Id -> a
errorVarNotInScope id = error $ "Var " ++ id ++ " not in scope"

errorAssigmnetsType :: Id -> GoValue -> GoType -> a
errorAssigmnetsType id v t = error $ baseErrorMessage ++ "x = expr, type x = " ++ showValueType v 
  ++ "; type expr = " ++ showType t

errorRedeclarationConst :: Id -> a
errorRedeclarationConst id = error $ "redeclaration const " ++ id

errorNotBoolInIf :: GoValue -> a
errorNotBoolInIf v = error $ baseErrorMessage ++ "not bool type in if: " ++ showValueType v 

errorAssignToConst :: Id -> a
errorAssignToConst id = error $ baseErrorMessage ++ "assign to const " ++ id

errorNotBoolExprInFor :: a
errorNotBoolExprInFor = error $ baseErrorMessage ++ "not bool expression in for"

errorIndexOutOfRange :: Int ->  a
errorIndexOutOfRange i = error $ baseErrorMessage ++ "index out of range: " ++ show i

internalErrorEmptyFrameStack :: a
internalErrorEmptyFrameStack = error $ baseInternalErrorMessage ++ "empty frame stack"