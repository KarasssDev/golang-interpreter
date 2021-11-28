open Typing

type id = string [@@deriving show { with_path = false }]

type infix_op =
  | Add
  | Sub
  | Mul
  | Div
  | Less
  | Leq
  | Gre
  | Geq
  | Eq
  | Neq
  | And
  | Or
[@@deriving show { with_path = false }]

and unary_op =
  | Minus
  | Not
[@@deriving show { with_path = false }]

and const =
  | CInt of int
  | CString of string
  | CBool of bool
[@@deriving show { with_path = false }]

and binding = bool * pat * exp [@@deriving show { with_path = false }]

and case = pat * exp

and exp =
  | EConst of const
  | EOp of infix_op * exp * exp
  | EUnOp of unary_op * exp
  | EVar of id
  | EList of exp list
  | ETuple of exp list
  | ECons of exp * exp
  | EIf of exp * exp * exp
  | ELet of binding list * exp
  | EFun of pat * exp
  | EApp of exp * exp
  | EMatch of exp * case list
[@@deriving show { with_path = false }]

and pat =
  | PWild
  | PVar of id
  | PConst of const
  | PCons of pat * pat
  | PList of pat list
  | PTuple of pat list
[@@deriving show { with_path = false }]

and decl =
  | DLet of binding
  | DEffect of id * tyexp
[@@deriving show { with_path = false }]

and prog = decl list [@@deriving show { with_path = false }]
