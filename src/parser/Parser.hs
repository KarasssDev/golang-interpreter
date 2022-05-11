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
  try semi
  GoProgram <$> statementList

-- statements 

statement :: Parser GoStatement
statement =
    try decl   <|>
    try gprint <|>
    try block  <|>
    try jump   <|>
    try ifelse <|>
    try gif    <|>
    try for    <|>
    try assign <|>
    try stExpr

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

-- assign

assign :: Parser GoStatement
assign = do
  id <- try identifier
  try $ reserved "="
  e <- try expr
  optional semi
  return $ Assign id e

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
gtype = try tint <|> try tbool <|> try tstring <|> try tchan <|>  return TNil

tint :: Parser GoType
tint = do
    try $ reserved "int"
    return TInt

tbool :: Parser GoType
tbool = do
    try $ reserved "bool"
    return TBool

tstring :: Parser GoType
tstring = do
    try $ reserved "string"
    return TString

tchan :: Parser GoType
tchan = do
    try $ reserved "chan"
    t <- try gtype
    return $ TChan t 

-- for
for :: Parser GoStatement
for = try for1 <|> try for2

for1 :: Parser GoStatement
for1 = do
  try $ reserved "for"
  try semi
  e <- try expr <|> return EmptyCondition
  try semi
  d <- try statement <|> return EmptyStatement
  b <- try block
  return $ For EmptyStatement e d b

for2 :: Parser GoStatement
for2 = do
  try $ reserved "for"
  try semi
  e <- try expr <|> return EmptyCondition
  try semi
  b <- try block
  return $ For EmptyStatement e EmptyStatement b

-- block

block :: Parser GoStatement
block = Block <$> braces statementList

statementList :: Parser [GoStatement]
statementList = many $ try statement

-- jump

jump :: Parser GoStatement
jump = Jump <$> (greturn <|> gbreak <|> continue)

greturn :: Parser JumpStatement
greturn = do
    try $ reserved "return"
    e <- try expr
    try semi
    return $ Return e

gbreak :: Parser JumpStatement
gbreak = do
  try $ reserved "break"
  try semi
  return Break

continue :: Parser JumpStatement
continue = do
  try $ reserved "continue"
  try semi
  return Continue

-- if else

gif :: Parser GoStatement
gif = do
  try $ reserved "if"
  e <- try expr
  b <- try block
  return $ If e b

ifelse :: Parser GoStatement
ifelse = do
  try $ reserved "if"
  e <- try expr
  b1 <- try block
  try $ reserved "else"
  b2 <- try statement
  return $ IfElse e b1 b2

-- expressions

expr :: Parser GoExpr
expr = Ex.buildExpressionParser table term

term :: Parser GoExpr
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

binary name fun = Ex.Infix   ( do { reservedOp name; return fun } )
prefix  name fun = Ex.Prefix  ( do { reservedOp name; return fun } )
postfix name fun = Ex.Postfix ( do { reservedOp name; return fun } )


binIntOp s op = binary s (GoBinOp op) Ex.AssocLeft
unIntOp  s op = prefix s (GoUnOp op)

compOp s op = binary s (GoBinOp op) Ex.AssocNone

binBoolOp s op = binary s (GoBinOp op) Ex.AssocLeft
unBoolOp s op = prefix s (GoUnOp op)

-- values 

value :: Parser GoExpr
value = Val <$> (vint <|> vbool <|> vstring)

vint :: Parser GoValue
vint = toVInt <$> integer
  where
    toVInt x = VInt $ fromInteger x

vbool :: Parser GoValue
vbool = (toVTrue <$> try (reserved "true")) <|> (toVFalse <$> try (reserved "false"))
  where
    toVTrue  _ = VBool True
    toVFalse _ = VBool False

vstring :: Parser GoValue
vstring = do
  syms <- try $ between (sym "\"") (sym "\"") (many letter)
  return $ VString syms

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
      if x == '\n' || x == '\t' then
        helper xs (' ':r)
      else
        helper xs (x:r)
    helper [] r = reverse r

goParse :: String -> Either ParseError GoProgram
goParse = parse program ""

pp :: String -> Either ParseError GoType
pp = parse gtype ""