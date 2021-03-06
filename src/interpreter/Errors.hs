module Errors where
import Ast
import Prelude hiding (lookup)
import Data.Map
import Types (getType)

-- errors

baseExceptionMessage :: String
baseExceptionMessage = "Interpretation error: "

baseInternalErrorMessage :: String
baseInternalErrorMessage = "Internal interpretation error: "

-- helpers for erros
showValueType :: GoValue -> String
showValueType v = showType $ getType v

showType :: GoType -> String
showType TInt    = "int"
showType TString = "string"
showType TBool   = "bool"
showType (TArray sz t)  = show sz ++ "array of " ++ showType t
showType (TChan t) = "chan " ++ showType t
showType (TFunc sign rt) = show sign ++ showType rt
showType TNil = "nil" 

-- Exceptions

exceptionUnexpectedType :: GoValue -> String -> String -> String
exceptionUnexpectedType v act t = 
    baseExceptionMessage ++ "unexpected type for " ++ act ++
    "\nexpected type: " ++ t ++
    "\nactual type: " ++ showValueType v

exceptionUnexpectedTypes :: GoValue -> GoValue -> BinOp -> String -> String -> String
exceptionUnexpectedTypes v1 v2 op t1 t2 = 
    baseExceptionMessage ++ "unexpected type for " ++ show op ++
    "\nexpected types: " ++ t1 ++ " " ++ t2 ++
    "\nactual types: " ++ showValueType v1 ++ " " ++ showValueType v2

exceptionVarNotInScope :: Id -> String
exceptionVarNotInScope idr = "Var " ++ idr ++ " not in scope"

exceptionAssigmnetsType :: Id -> GoValue -> GoType -> String
exceptionAssigmnetsType idr v t = baseExceptionMessage ++ "x = expr, type x = " ++ showValueType v
  ++ "; type expr = " ++ showType t

exceptionRedeclarationConst :: Id -> String
exceptionRedeclarationConst idr = "redeclaration const " ++ idr

exceptionNotBoolInIf :: GoValue -> String
exceptionNotBoolInIf v = baseExceptionMessage ++ "not bool type in if: " ++ showValueType v

exceptionAssignToConst :: Id -> String
exceptionAssignToConst idr = baseExceptionMessage ++ "assign to const " ++ idr

exceptionNotBoolExprInFor :: String
exceptionNotBoolExprInFor = baseExceptionMessage ++ "not bool expression in for"

exceptionIndexOutOfRange :: Int -> String
exceptionIndexOutOfRange i = baseExceptionMessage ++ "index out of range: " ++ show i

exceptionCallNotFunc :: String -> String
exceptionCallNotFunc name = baseExceptionMessage ++ name ++ "is not func" 

exceptionExpectedCodeBlock :: String -> String
exceptionExpectedCodeBlock name = baseExceptionMessage ++ "expected code block after declatration func " ++ name 

exceptionTypeNotSubscriptable :: GoType -> String
exceptionTypeNotSubscriptable t = baseExceptionMessage ++ showType t ++ "doesnt subscriptable"

exceptionExpectedChv :: GoValue -> String
exceptionExpectedChv v = baseExceptionMessage ++ "expected: chan t, actual: " ++  showType (getType v)

exceptionExpectedCht :: GoType -> String
exceptionExpectedCht t = baseExceptionMessage ++ "expected: chan t, actual: " ++  showType t

-- errrors

internalErrorEmptyFrameStack :: String
internalErrorEmptyFrameStack = baseInternalErrorMessage ++ "empty frame stack"

internalErrorEmptyScopes :: String
internalErrorEmptyScopes = baseInternalErrorMessage ++ "empty scope list"

unexpectedInternalError :: a
unexpectedInternalError = error $ baseInternalErrorMessage ++ "unexpexted error"