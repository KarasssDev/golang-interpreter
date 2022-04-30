module BaseFunc where
import Ast
import Errors

instance (Eq GoValue) where
  VInt x == VInt y = x == y
  VString x == VString y = x == y
  VBool x == VBool y = x == y
  VArray x xs == VArray y ys = x == y && xs == ys
  x == y = unexpectedInternalError

instance (Ord GoValue) where
    compare (VInt x) (VInt y) = compare x y
    compare x y = unexpectedInternalError

instance (Num GoValue) where
  VInt x + VInt y = VInt $ x + y
  VString x + VString y = VString $ x ++ y
  x + y = unexpectedInternalError

  VInt x * VInt y = VInt $ x * y
  x * y = unexpectedInternalError

  abs (VInt x) = VInt $ abs  x
  abs x = unexpectedInternalError

  signum (VInt x ) = VInt $ signum x
  signum x = unexpectedInternalError

  fromInteger x = VInt $ fromInteger x

  negate (VInt x) = VInt $ negate x
  negate x = unexpectedInternalError

instance (Real GoValue) where
  toRational (VInt x) = toRational x
  toRational x = unexpectedInternalError

instance (Enum GoValue) where
  toEnum x = VInt x

  fromEnum (VInt x) = fromEnum x
  fromEnum x = unexpectedInternalError


instance (Integral GoValue) where
  quotRem (VInt x) (VInt y) = (x', y')
      where
          x' = VInt $ fst $ x `quotRem` y
          y' = VInt $ snd $ x `quotRem` y
  quotRem x y = unexpectedInternalError

  toInteger (VInt x) = toInteger x
  toInteger x = unexpectedInternalError


-- implement func

-- bool
goAnd :: GoValue -> GoValue -> GoValue
goAnd (VBool x) (VBool y) = VBool $ x && y
goAnd x y = unexpectedInternalError

goOr :: GoValue -> GoValue -> GoValue
goOr (VBool x) (VBool y) = VBool $ x || y
goOr x y = unexpectedInternalError

goNot :: GoValue  -> GoValue
goNot (VBool x) = VBool  $ not x
goNot x = unexpectedInternalError

-- for Print functionality 

class (Printable a) where
  toPrint :: a -> String

instance (Printable BinOp) where -- for print in errors
  toPrint op = case op of
    Add -> "+"
    Minus -> "-"
    Mul -> "*"
    Div -> "/"
    Mod -> "%"
    And -> "&&"
    Or -> "||"
    Eq -> "=="
    Gr -> ">"
    Le -> "<"
    Gre -> ">="
    Leq -> "<="
    Neq -> "!="

instance (Printable GoValue) where
  toPrint x = case x of 
    (VInt v)       -> show v
    (VString v)    -> v
    (VBool True)   -> "true"
    (VBool False)  -> "false" 
    VNil           -> "Nil"
    _ -> unexpectedInternalError