module Interpreter where
import Prelude hiding (lookup)
import Ast
import Control.Monad.State
import Data.Map (Map, lookup, empty, insert)

-- errors

baseErrorMessage :: String
baseErrorMessage = "Interpretation error: "

-- helpers for erros
showType :: GoValue -> String
showType (VInt _)    = "int"
showType (VString _) = "string"
showType (VBool _)   = "bool"
showType (VArray x)  = "array of " ++ showType (head x)


errorUnexpectedType :: GoValue -> String -> String -> a
errorUnexpectedType v act t = error $
    baseErrorMessage ++ "unexpected type for " ++ act ++
    "\nexpected type: " ++ t ++
    "\nactual type: " ++ showType v

errorUnexpectedTypes :: GoValue -> GoValue -> String -> String -> String -> a
errorUnexpectedTypes v1 v2 act t1 t2 = error $
    baseErrorMessage ++ "unexpected type for " ++ act ++
    "\nexpected types: " ++ t1 ++ " " ++ t2 ++
    "\nactual types: " ++ showType v1 ++ " " ++ showType v2

errorVarNotInScope :: Id -> a
errorVarNotInScope id = error $ "Var " ++ id ++ " not in scope"

-- implement base classes

instance (Eq GoValue) where
  VInt x == VInt y = x == y
  VString x == VString y = x == y
  VBool x == VBool y = x == y
  VArray x == VArray y = x == y
  x == y = errorUnexpectedTypes x y "==" "t" "t"


instance (Ord GoValue) where
    compare (VInt x) (VInt y) = compare x y
    compare x y = errorUnexpectedTypes x y "compare" "int" "int"


instance (Num GoValue) where
  VInt x + VInt y = VInt $ x + y
  x + y = errorUnexpectedTypes x y "+" "int" "int"

  VInt x * VInt y = VInt $ x * y
  x * y = errorUnexpectedTypes x y "*" "int" "int"

  abs (VInt x) = VInt $ abs  x
  abs x = errorUnexpectedType x "abs" "int"

  signum (VInt x ) = VInt $ signum x
  signum x = errorUnexpectedType x "signum" "int"

  fromInteger x = VInt $ fromInteger x

  negate (VInt x) = VInt $ negate x
  negate x = errorUnexpectedType x "-" "int"

instance (Real GoValue) where
  toRational (VInt x) = toRational x
  toRational x = errorUnexpectedType x "toRational" "int"

instance (Enum GoValue) where
  toEnum x = VInt x

  fromEnum (VInt x) = fromEnum x
  fromEnum x = errorUnexpectedType x "fromEnum" "int"


instance (Integral GoValue) where
  quotRem (VInt x) (VInt y) = (x', y')
      where
          x' = VInt $ fst $ x `quotRem` y
          y' = VInt $ snd $ x `quotRem` y
  quotRem x y = errorUnexpectedTypes x y "quotRem" "int" "int"

  toInteger (VInt x) = toInteger x
  toInteger x = errorUnexpectedType x "toInteger" "int"


-- implement func

-- bool
goAnd :: GoValue -> GoValue -> GoValue
goAnd (VBool x) (VBool y) = VBool $ x && y
goAnd x y = errorUnexpectedTypes x y "&&" "bool" "bool"

goOr :: GoValue -> GoValue -> GoValue
goOr (VBool x) (VBool y) = VBool $ x || y
goOr x y = errorUnexpectedTypes x y "||" "bool" "bool"

goNot :: GoValue  -> GoValue
goNot (VBool x) = VBool  $ not x
goNot x = errorUnexpectedType x "not" "bool"

-- runtime struct

data GoRuntime = GoRuntime {
    vars :: Map Id GoValue,
    consts :: Map Id GoValue,
    toPrint :: [String]
}

emptyGoRuntime :: GoRuntime
emptyGoRuntime = GoRuntime {vars = empty , consts = empty, toPrint=[] }

getOrError :: Id -> GoRuntime -> GoValue
getOrError id r = case lookup id (vars r) of
    Just e -> e
    Nothing -> errorVarNotInScope id


-- runtime monad

type Runtime a = State GoRuntime a

getVar :: Id -> Runtime GoValue
getVar id = gets (getOrError id)

putVar :: Id -> GoValue -> Runtime ()
putVar id v = do
  r <- get
  put GoRuntime {vars = insert id v (vars r), consts = consts r, toPrint = toPrint r}

goPrint :: GoValue -> Runtime ()
goPrint v = do
  r <- get
  put GoRuntime {vars = vars r, consts = consts r, toPrint = show v : toPrint r}

-- eval expr


getValue :: Runtime GoValue  -> GoValue
getValue r = evalState r emptyGoRuntime



evalExpr :: GoExpr -> GoRuntime -> GoValue
-- int
evalExpr (Add   e1 e2) r = evalExpr e1 r   +   evalExpr e2 r
evalExpr (Minus e1 e2) r = evalExpr e1 r   -   evalExpr e2 r
evalExpr (Mul   e1 e2) r = evalExpr e1 r   *   evalExpr e2 r
evalExpr (Div   e1 e2) r = evalExpr e1 r `div` evalExpr e2 r
evalExpr (Mod   e1 e2) r = evalExpr e1 r `mod` evalExpr e2 r
evalExpr (UnMinus e)   r = - evalExpr e r
-- bool 
evalExpr (And e1 e2) r = evalExpr e1 r `goAnd` evalExpr e2 r
evalExpr (Or  e1 e2) r = evalExpr e1 r `goOr`  evalExpr e2 r
evalExpr (Not e)     r = goNot $ evalExpr e r
-- comparsions
evalExpr (Eq  e1 e2) r = VBool $ evalExpr e1 r == evalExpr e2 r
evalExpr (Gr  e1 e2) r = VBool $ evalExpr e1 r >  evalExpr e2 r
evalExpr (Le  e1 e2) r = VBool $ evalExpr e1 r <  evalExpr e2 r
evalExpr (Gre e1 e2) r = VBool $ evalExpr e1 r >= evalExpr e2 r
evalExpr (Leq e1 e2) r = VBool $ evalExpr e1 r <= evalExpr e2 r
evalExpr (Neq e1 e2) r = VBool $ evalExpr e1 r /= evalExpr e2 r
-- other
evalExpr (Val x) r = x
evalExpr (Var id) r = getOrError id r
evalExpr _ _ = undefined


-- eval statement

evalStatement :: GoStatement -> Runtime ()

evalStatement (VarDecl id t e) = do
  r <- get
  putVar id (evalExpr e r)

evalStatement (Block b) = case b of
  [] -> error "empty block"
  [x] -> evalStatement x
  x:xs -> do
     evalStatement x
     evalStatement (Block xs)

evalStatement (Print e) = do
  r <- get
  goPrint $ evalExpr e r

evalStatement _ = undefined
