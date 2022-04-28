module Ast where
import Data.Map

type Id = String

data GoType =  -- t
      TInt                       -- int
    | TString                    -- string
    | TBool                      -- bool
    | TArray Int GoType          -- arr[size] type
    | TChan GoType               -- chan int
    | TFunc [(Id,GoType)] GoType -- func (int x, int y) int
    | TNil
    deriving Show

data GoValue =
      VInt Int
    | VString String
    | VBool Bool
    | VArray (Map Int GoValue)
    | VChan Int
    | VFunc [(Id, GoType)] GoStatement
    | VNil

instance (Show GoValue) where
  show x = case x of 
    (VInt v)       -> show v
    (VString v)    -> v
    (VBool True)   -> "true"
    (VBool False)  -> "false" 
    VNil           -> "Nil"
    _ -> undefined -- TODO

data BinOp = 
-- int
    Add   -- +
  | Minus -- -
  | Mul   -- *
  | Div   -- /
  | Mod   -- %
-- bool 
  | And -- &&
  | Or  -- ||
-- comparsions
  | Eq  -- ==
  | Gr  -- >
  | Le  -- <
  | Gre -- >=
  | Leq -- <=
  | Neq -- !=
  deriving Show

data UnOp = 
    UnMinus -- -int
  | Not     -- !bool
  deriving Show

data GoExpr = -- e
      GoUnOp UnOp GoExpr          -- op e
    | GoBinOp BinOp GoExpr GoExpr -- e1 op e2
    | Get -- TODO
    | Put -- TODO
    | Var Id                      -- x
    | FuncCall Id [GoExpr]        -- f(e1,...,en)
    | GoFuncCall Id [GoExpr]      -- go f(e1,...,en)
    | GetByInd GoExpr GoExpr      -- arr[e] (arr is e)
    | Val GoValue                 -- 3 = Val (VInt 3)
    | EmptyCondition              -- for s;;s (empty condition in for loop)
    deriving Show


data JumpStatement = -- j
    Break         -- break
  | Continue      -- continue
  | Return GoExpr -- return e
  deriving Show

data GoStatement = -- s
      VarDecl Id GoType GoExpr                       -- var x t = 
    | ConstDecl Id GoType GoExpr                     -- const x t = 
    | FuncDecl Id [(Id, GoType)] GoType GoStatement  -- func f(x1 t1, ..., xn tn) t b
    | Expr GoExpr                                    -- for func calls
    | Block [GoStatement]                            -- { s1; ... ; sn; } = b
    | If GoExpr GoStatement                          -- if e b
    | IfElse GoExpr GoStatement GoStatement          -- if e b1 else b2
    | For GoStatement GoExpr GoStatement GoStatement -- for s;e;s { s1; ... ; sn; }
    | Print GoExpr                                   -- println(e)
    | Assign Id GoExpr                               -- x = e
    | SetByInd Id GoExpr GoExpr                      -- arr[e1] = e2 
    | EmptyStatement                                 -- for ;e; (empty statement in for loop)
    | Jump JumpStatement                             -- j
    deriving Show

newtype GoProgram = GoProgram [GoStatement] deriving Show