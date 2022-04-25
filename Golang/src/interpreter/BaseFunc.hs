module BaseFunc where
import Ast
import Errors

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
  VString x + VString y = VString $ x ++ y
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