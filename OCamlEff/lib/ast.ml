open Typing

type id = string [@@deriving show { with_path = false }] (*  var_name  *)

type infix_op =
  | Add  (*  +   *)
  | Sub  (*  -   *)
  | Mul  (*  *   *)
  | Div  (*  /   *)
  | Less (*  <   *)
  | Leq  (*  <=  *)
  | Gre  (*  >   *)
  | Geq  (*  >=  *)
  | Eq   (*  =   *)
  | Neq  (*  <>  *)
  | And  (*  &&  *)
  | Or   (*  ||  *)
[@@deriving show { with_path = false }]

and unary_op =
  | Minus (*  -    *)
  | Not   (*  not  *)
[@@deriving show { with_path = false }]

and const =
  | CInt of int       (*    1    *)
  | CString of string (*  "abc"  *)
  | CBool of bool     (*  true   *)
[@@deriving show { with_path = false }]

and binding = bool * pat * exp [@@deriving show { with_path = false }]

and case = pat * exp
(*  | _ :: [] -> 5  *)

and exp =
  | EConst of const             (*    1                       *)
  | EOp of infix_op * exp * exp (*    1 + 1                   *)
  | EUnOp of unary_op * exp     (*    -1                      *)
  | EVar of id                  (*    hey                     *)
  | EList of exp list           (*    [1; 2]                  *)
  | ETuple of exp list          (*    1, 2                    *)
  | ECons of exp * exp          (*    hd :: tl                *)
  | EIf of exp * exp * exp      (*    if true then 1 else 0   *)
  | ELet of binding list * exp  (*    let x = 5 in 10         *)
  | EFun of pat * exp           (*    fun x -> x * 2          *)
  | EApp of exp * exp           (*    f x                     *)
  | EMatch of exp * case list   (*    match e with | _ -> 0   *)
  | EPerform of pat * exp
  | EContinue of cont_val * exp
[@@deriving show { with_path = false }]

and pat =
  | PWild              (*  _         *)
  | PVar of id         (*  abc       *)
  | PConst of const    (*  1         *)
  | PCons of pat * pat (*  hd :: tl  *)
  | PList of pat list  (*  [a; b]    *)
  | PTuple of pat list (*  a, b      *)
  | PEffect of eff * (pat list)
  | PEffectH of pat * cont_val
[@@deriving show { with_path = false }]

and decl =
  | DLet of binding       (*  let x = 10                *)
  | DEffect of id * tyexp (*  effect E : string -> int  *)
[@@deriving show { with_path = false }]

and cont_val = Continuation of id [@@deriving show { with_path = false }]

and eff = id [@@deriving show { with_path = false }]

and prog = decl list [@@deriving show { with_path = false }]
