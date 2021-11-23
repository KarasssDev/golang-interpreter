open Typing

type id = string [@@deriving show { with_path = false }]

type infix_op =
  | Add
  | Sub
  | Mul
  | Div
  | Leq
  | Eq
  | And
  | Or
  | Con
[@@deriving show { with_path = false }]

and unary_op = 
  | Plus 
  | Minus

and const =
  | CInt of int
  | CString of string
  | CBool of bool
[@@deriving show { with_path = false }]

and exp =
  | EConst of const
  | EOp of infix_op * exp * exp
  | EUnOp of unary_op * exp
  | EVar of id
  | EList of exp list
  | ETuple of exp list
  | EIf of exp * exp * exp
  | ELet of pat * (pat * exp) list * exp
  | ELetRec of pat * (pat * exp) list * exp
  | EFun of pat * exp
  | EApp of exp * exp
  | EMatch of exp * (pat * exp) list
[@@deriving show { with_path = false }]

and pat =
  | PWild
  | PVar of id
  | PConst of const
  | PList of pat list
  | PTuple of pat list
[@@deriving show { with_path = false }]

and decl =
  | DLet of pat * exp
  | DLetRec of pat * exp
  | DEffect of id * type_exp
[@@deriving show { with_path = false }]

and prog = decl list [@@deriving show { with_path = false }]
