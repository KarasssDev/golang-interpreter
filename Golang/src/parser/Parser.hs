module Parser where 

import Lexer 
import Ast

import Data.Maybe
import Text.Parsec
import Text.Parsec.String (Parser)
import Control.Applicative ((<$>))

import qualified Text.Parsec.Expr as Ex
import qualified Text.Parsec.Token as Tok

-- program 

program :: Parser GoProgram
program = do
  skipMany1 (try $ reserved "package")
  skipMany1 (try $ reserved "main")
  GoProgram <$> (try statementList)

-- statements 

statement :: Parser GoStatement
statement = 
    try decl   <|> 
    try stExpr <|>
    try gprint <|>
    try block  <|>
    try jump   <|>
    try gif

-- declarations

decl :: Parser GoStatement
decl = try varDecl <|> try constDecl <|> try funcDecl

varDecl :: Parser GoStatement
varDecl = do
    try $ reserved "var" 
    id <- try identifier
    t  <- try gtype
    try $ reserved "="
    e  <- try expr
    try semi
    return $ VarDecl id t e

constDecl :: Parser GoStatement
constDecl = do
    try $ reserved "const" 
    id <- try identifier
    t  <- try gtype
    try $ reserved "="
    e  <- try expr
    try semi
    return $ ConstDecl id t e

funcDecl :: Parser GoStatement
funcDecl = do
    try $ reserved "func"
    id <- try identifier
    args <- try signs
    t <- try gtype
    body <- try block
    return $ FuncDecl id args t body

signs :: Parser [(Id, GoType)]
signs = parens $ commaSep (try sign)

sign :: Parser (Id, GoType)
sign = do
    id <- try identifier
    t <- try gtype
    return (id, t)

-- expr as statement

stExpr :: Parser GoStatement
stExpr = do
    e <- try expr
    try semi
    return $ Expr e

-- print 

gprint :: Parser GoStatement
gprint = do
    try $ reserved "println"
    e <- try $ parens $ try expr
    try semi
    return $ Print e

-- type

gtype :: Parser GoType
gtype = try tint <|> try tbool <|> (return TNil)

tint :: Parser GoType
tint = do
    try $ reserved "int" 
    return $ TInt

tbool :: Parser GoType
tbool = do
    try $ reserved "bool"
    return $ TBool

-- block

block :: Parser GoStatement
block = Block <$> braces statementList

statementList :: Parser [GoStatement]
statementList = many $ try statement

-- jump

jump :: Parser GoStatement
jump = Jump <$> greturn
 
greturn :: Parser JumpStatement
greturn = do
    try $ reserved "return"
    e <- try expr
    try semi
    return $ Return e

-- if else

gif :: Parser GoStatement
gif = do
  try $ reserved "if"
  e <- try expr
  b <- try block
  return $ If e b

-- expressions

expr = Ex.buildExpressionParser table term 

term = parens (try expr) <|> try value <|> try funcCall <|> try var 

-- operations

table = [ [ unIntOp "-" UnMinus,
            unBoolOp "!" Not]
        , [ binIntOp "*" Mul, 
            binIntOp "/" Div,
            binIntOp "%" Mod]
        , [ binIntOp "+" Add, 
            binIntOp "-" Minus]
        , [ compOp "==" Eq,
            compOp ">" Gr,
            compOp "<" Le,
            compOp ">=" Gre,
            compOp "<=" Leq,
            compOp "!=" Neq]
        , [ binBoolOp "&&" And ]
        , [ binBoolOp "||" Or ]
        ]

binary  name fun assoc = Ex.Infix   ( do { reservedOp name; return fun } ) assoc
prefix  name fun       = Ex.Prefix  ( do { reservedOp name; return fun } )
postfix name fun       = Ex.Postfix ( do { reservedOp name; return fun } )


binIntOp s op = binary s (GoBinOp op) Ex.AssocLeft
unIntOp  s op = prefix s (GoUnOp op) 

compOp s op = binary s (GoBinOp op) Ex.AssocNone

binBoolOp s op = binary s (GoBinOp op) Ex.AssocLeft
unBoolOp s op = prefix s (GoUnOp op) 

-- values 

value :: Parser GoExpr
value = Val <$> (vint <|> vbool)

vint :: Parser GoValue
vint = toVInt <$> integer
  where
    toVInt x = VInt $ fromInteger x

vbool :: Parser GoValue
vbool = (toVTrue <$> try (reserved "true")) <|> (toVFalse <$> try (reserved "false"))
  where
    toVTrue  _ = VBool True
    toVFalse _ = VBool False

-- var

var :: Parser GoExpr
var = Var <$> identifier

-- func call
funcCall :: Parser GoExpr
funcCall = do
    id <- try identifier
    args <- parens $ try listExpr
    return $ FuncCall id args

listExpr :: Parser [GoExpr]
listExpr = commaSep $ try expr


-- parse

cleanFile :: String -> String
cleanFile s = helper s ""
  where 
    helper (x:xs) r = 
      if (x == '\n' || x == '\t') then 
        helper xs (' ':r)
      else
        helper xs (x:r)
    helper [] r = reverse r

goParse :: String -> Either ParseError GoProgram
goParse inp = parse program "" inp

p s = parseTest statementList s