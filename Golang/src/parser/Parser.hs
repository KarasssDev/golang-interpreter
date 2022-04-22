module Parser where 

import Lexer 
import Ast

import Data.Maybe
import Text.Parsec
import Text.Parsec.String (Parser)
import Control.Applicative ((<$>))

import qualified Text.Parsec.Expr as Ex
import qualified Text.Parsec.Token as Tok



expr = Ex.buildExpressionParser table term <?> "expression"

term = parens expr <|> value <?> "simple expression"

-- operations

table = [ [ unIntOp "-" UnMinus]
        , [ binIntOp "*" Mul, 
            binIntOp "/" Mul ]
        , [ binIntOp "+" Mul, 
            binIntOp "-" Mul ]
        , [ compOp "==" Eq,
            compOp "<" Le ]
        ]

binary  name fun assoc = Ex.Infix   ( do { reservedOp name; return fun } ) assoc
prefix  name fun       = Ex.Prefix  ( do { reservedOp name; return fun } )
postfix name fun       = Ex.Postfix ( do { reservedOp name; return fun } )


binIntOp s op = binary s (GoBinOp op) Ex.AssocLeft
unIntOp  s op = prefix s (GoUnOp op) 
compOp s op = binary s (GoBinOp op) Ex.AssocNone

-- values 

value :: Parser GoExpr
value = Val <$> (vint <|> vbool)

vint :: Parser GoValue
vint = toVInt <$> integer
  where
    toVInt x = VInt $ fromInteger x

vbool :: Parser GoValue
vbool = (toVTrue <$> reserved "true") <|> (toVFalse <$> reserved "false")
  where
    toVTrue  _ = VBool True
    toVFalse _ = VBool False

p s = parse expr "" s 
