module Types where

import Ast

getType :: GoValue -> GoType
getType (VInt _)      = TInt
getType (VBool _)     = TBool
getType (VString _)   = TString
getType (VArray mp sizes)   = undefined
getType (VChan x t)   = TChan t
getType (VFunc signs t _) = TFunc signs t
getType VNil = TNil

typeCheckVT :: GoValue -> GoType -> Bool
typeCheckVT v t = getType v == t

typeCheckVV :: GoValue -> GoValue -> Bool
typeCheckVV v1 v2 = getType v1 == getType v2




