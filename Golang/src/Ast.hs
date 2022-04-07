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

data GoExpr = 
    -- int 
      Add GoExpr GoExpr   -- (+)
    | Minus GoExpr GoExpr -- (-)
    | Mul GoExpr GoExpr   -- (*)
    | Div GoExpr GoExpr   -- (/)
    | Mod GoExpr GoExpr   -- (%)
    | UnMinus GoExpr      -- (-)
    -- bool
    | And GoExpr GoExpr -- (&&)
    | Or GoExpr GoExpr  -- (||)
    | Not GoExpr        -- (!)
    -- comparsions
    | Eq GoExpr GoExpr  -- (==)
    | Gr GoExpr GoExpr  -- (>)
    | Le GoExpr GoExpr  -- (<)
    | Gre GoExpr GoExpr -- (>=)
    | Leq GoExpr GoExpr -- (<=)
    | Neq GoExpr GoExpr -- (!=)
    -- chan
    | Get -- пока здесь для напоминания
    | Put --пока здесь для напоминания
    -- other
    | Var Id
    | FuncCall Id [GoExpr]
    | GoFuncCall Id [GoExpr]
    | Val GoValue
    deriving Show


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
    deriving Show

data GoProgram = 
      Top GoStatement
    | Main GoStatement