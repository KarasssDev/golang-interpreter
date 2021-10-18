type identifier = string

type arithop = Add | Sub | Mul | Div 

type boolop = And | Or

type boolexpr = 
  | True 
  | False 
  | BoolOp of boolop * boolexpr * boolexpr
  
type arithexpr = 
  | Int of int
  | ArithOp of arithop * arithexpr * arithexpr

type expr = 
  | Var of identifier
  | Bool of boolexpr
  | Number of arithexpr
  | LetBind of identifier * expr
  | LetBindIn of identifier * expr * expr