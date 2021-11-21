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

type const =
  | Int of int
  | Char of char
  | String of string
  | Bool of bool
[@@deriving show { with_path = false }]

and exp =
  | EConst of const
  | EOp of infix_op * exp * exp
  | EVar of id
  | EList of exp list
  | EIf of exp * exp * exp
  | ELet of (pat * exp) list * exp
  | ELetRec of (pat * exp) list * exp
  | EFun of pat * exp
  | EApp of exp * exp
  | EMatch of exp * (pat * exp) list
[@@deriving show { with_path = false }]

and pat =
  | PWild
  | PVar of id
  | PConst of const
  | PList of pat list
[@@deriving show { with_path = false }]

and decl =
  | DLet of pat * exp
  | DLetRec of pat * exp
  | DEffect of id * type_exp
[@@deriving show { with_path = false }]
