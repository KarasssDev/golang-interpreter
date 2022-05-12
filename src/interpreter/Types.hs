module Types where

import Ast
import Prelude hiding (lookup)
import Data.Map (lookup)

getType :: GoValue -> GoType
getType (VInt _)      = TInt
getType (VBool _)     = TBool
getType (VString _)   = TString
getType arr@(VArray mp sizes)   = TArray sizes (getArrayElemType arr)
getType (VChan t _)   = TChan t
getType (VFunc signs t _) = TFunc signs t
getType VNil = TNil

getArrayElemType :: GoValue -> GoType
getArrayElemType (VArray mp sizes) = case lookup 0 mp of
    Just v  -> getType v
    Nothing -> error "0 sizes array"
getArrayElemType _ = error "must call only for arrays" -- fix me


typeCheckVT :: GoValue -> GoType -> Bool
typeCheckVT v t = getType v == t

typeCheckVV :: GoValue -> GoValue -> Bool
typeCheckVV v1 v2 = getType v1 == getType v2




