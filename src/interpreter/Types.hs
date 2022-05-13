module Types where

import Ast
import Prelude hiding (lookup)
import Data.Map (lookup)

getType :: GoValue -> GoType
getType (VInt _)      = TInt
getType (VBool _)     = TBool
getType (VString _)   = TString
getType arr@(VArray mp sizes t)   = TArray sizes t
getType (VChan t _)   = TChan t
getType (VFunc signs t _) = TFunc signs t
getType VNil = TNil

typeCheckVT :: GoValue -> GoType -> Bool
typeCheckVT v t = getType v == t

typeCheckVV :: GoValue -> GoValue -> Bool
typeCheckVV v1 v2 = getType v1 == getType v2




