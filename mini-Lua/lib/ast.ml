exception Unbound_Variable of string

type arop = Sum | Sub | Mul | Div | FDiv | Mod [@@deriving show { with_path = false }]

type logop = And | Or [@@deriving show { with_path = false }]

type unop = Not [@@deriving show { with_path = false }]

type relop = Eq | Neq | Le | Leq | Ge | Geq [@@deriving show { with_path = false }]

type name = string [@@deriving show { with_path = false}]

type value =
  | VBool of bool
  | VInt of int 
  | VFloat of float
  | VString of string
  | VTable of (name, value) Hashtbl.t
  | VNull
(* [@@deriving show { with_path = false }] *)

type expr = 
  | Const of value
  | Var of name 
  | ArOp of arop * expr * expr
  | LogOp of logop * expr * expr 
  | UnOp of unop * expr
  | RelOp of relop * expr * expr
  | TableAccess of expr * expr 
  | TableCreate of expr list
  | CallFunc of expr * expr list
  | Assign of expr * expr
(* [@@deriving show { with_path = false }] *)

type statement =
   | If of (expr * statement) list
   | While of expr * statement 
   | ForNumerical of expr * expr list * statement (* for a(expr) = 1, 5, 2 (expr list) do <(statement)> end *)
   | Break 
   | Local of statement
   | Return of expr
   | VarDec of (expr * expr) list 
   | Expression of expr
   | Block of statement list
   | FuncDec of name * (name list) * statement (* func_name * args * block *)
(* [@@deriving show { with_path = false }] *)