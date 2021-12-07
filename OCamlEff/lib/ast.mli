type ident = string (*  var_name  *)

type capitalized_ident = string
(*  Choice  *)

type binder = int

type tyexp =
  | TInt (*   int   *)
  | TBool (*   bool   *)
  | TString (*   string   *)
  | TList of tyexp (*   int list list   *)
  | TTuple of tyexp list (*   int list * string   *)
  | TVar of binder (*   1 (polymorphic type)   *)
  | TArrow of tyexp * tyexp
(*   string -> int   *)

type infix_op =
  | Add (*  +   *)
  | Sub (*  -   *)
  | Mul (*  *   *)
  | Div (*  /   *)
  | Less (*  <   *)
  | Leq (*  <=  *)
  | Gre (*  >   *)
  | Geq (*  >=  *)
  | Eq (*  =   *)
  | Neq (*  <>  *)
  | And (*  &&  *)
  | Or
(*  ||  *)

and unary_op =
  | Minus
  (*  - *)
  | Not
(*  not  *)

and const =
  | CInt of int (*    1    *)
  | CString of string (*  "abc"  *)
  | CBool of bool
(*  true   *)

and binding = bool * pat * exp

and case = pat * exp
(*  | _ :: [] -> 5  *)

and exp =
  | EConst of const (*    true    *)
  | EOp of infix_op * exp * exp (*    1 / (2 + 3)    *)
  | EUnOp of unary_op * exp (*    not predicate    *)
  | EVar of ident (*    x    *)
  | EList of exp list (*    [x; y; z]    *)
  | ETuple of exp list (*    x, y, z    *)
  | ECons of exp * exp (*    x :: xs    *)
  | EIf of exp * exp * exp (*    if predicate then x else y    *)
  | ELet of binding list * exp (*    let x = 5 in 10    *)
  | EFun of pat * exp (*    fun x,y,z -> x + y * z    *)
  | EApp of exp * exp (*    fold f list init    *)
  | EMatch of exp * case list (*    match lst with [] -> 0 | hd :: tl -> hd    *)
  | EPerform of effect * exp (*    perform (Choice x)   *)
  | EContinue of continuation * exp
(*    continue k (x - 1)    *)

and continuation = Continuation of ident

and effect = Effect of capitalized_ident

and pat =
  | PWild (*  _  *)
  | PVar of ident (*  abc   *)
  | PConst of const (*  1   *)
  | PCons of pat * pat (*  hd :: tl  *)
  | PList of pat list (*  [a; b]  *)
  | PTuple of pat list (*  a, b   *)
  | PEffectH of effect * pat * continuation

and decl =
  | DLet of binding
  (*  let x = 10   *)
  | DEffect of ident * tyexp
(*  effect E : int -> int  *)

and prog = decl list
