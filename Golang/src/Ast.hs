module Ast where

type Id = String

data GoType = 
      TInt                  -- int
    | TString               -- string
    | TBool                 -- bool
    | TArray Int GoType     -- arr[size] type
    | TChan GoType          -- chan int
    | TFunc [(Id,GoType)] GoType -- func (int x, int y) int
    deriving Show

data GoValue =
      VInt Int
    | VString String
    | VBool Bool
    | VArray [GoValue]
    deriving Show

data BinOp = 
-- int
    Add 
  | Minus 
  | Mul 
  | Div
  | Mod
-- bool 
  | And 
  | Or   
-- comparsions
  | Eq
  | Gr
  | Le
  | Gre
  | Leq
  | Neq
  deriving Show

data UnOp = 
    UnMinus -- int
  | Not     -- bool
  deriving Show

data GoExpr = 
      GoUnOp UnOp GoExpr
    | GoBinOp BinOp GoExpr GoExpr
    | Get -- пока здесь для напоминания
    | Put --пока здесь для напоминания
    | Var Id
    | FuncCall Id [GoExpr]
    | GoFuncCall Id [GoExpr]
    | Val GoValue
    | EmptyCondition
    deriving Show


data JumpStatement = Break | Continue deriving Show

data GoStatement = 
      VarDecl Id GoType GoExpr   -- var x int = 
    | ConstDecl Id GoType GoExpr -- const x int = 
    | FuncDecl Id [(Id, GoType)] GoType GoStatement
    | Expr GoExpr
    | Block [GoStatement]
    | Return GoExpr
    | If GoExpr GoStatement
    | IfElse GoExpr GoStatement GoStatement
    | For GoStatement GoExpr GoStatement GoStatement
    | Print GoExpr
    | Assign Id GoExpr
    | EmptyStatement
    | Jump JumpStatement
    deriving Show

data GoProgram = 
      Top GoStatement
    | Main GoStatement