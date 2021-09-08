open Hashtbl_p

type arop = Sum | Sub | Mul | Div | FDiv | Mod
[@@deriving show {with_path= false}]

type logop = And | Or [@@deriving show {with_path= false}]
type unop = Not [@@deriving show {with_path= false}]

type relop = Eq | Neq | Le | Leq | Ge | Geq
[@@deriving show {with_path= false}]

type name = string [@@deriving show {with_path= false}]

type value =
  | VBool of bool
  | VNumber of float
  | VString of string
  | VTable of (name, value) Hashtbl_p.t
  | VFunction of name list * statement (* name list -- function arguments, statement -- function body*)
  | VNull
[@@deriving show {with_path= false}]

and expr =
  | Const of value
  | Var of name
  | ArOp of arop * expr * expr
  | LogOp of logop * expr * expr
  | UnOp of unop * expr
  | RelOp of relop * expr * expr
  | TableAccess of name * expr (* name[expr], where 'name' is name of the table *)
  | TableCreate of expr list (* Lua supports table constructor like {1, 2, a = 4}*)
  | CallFunc of name * expr list (* name([expr list]), where 'name' is name of the function and 'expr list' is passed arguments*)
  | Assign of expr * expr
[@@deriving show {with_path= false}]

and statement =
  | If of (expr * statement) list
  | While of expr * statement
  | ForNumerical of name * expr list * statement (* for a(expr) = 1, 5, 2 (expr list) do <(statement)> end *)
  | Break
  | Local of statement
  | Return of expr
  | VarDec of (expr * expr) list
  | Expression of expr
  | Block of statement list
  | FuncDec of name * name list * statement (* name -- name of function, name list -- function arguments, statement -- function body*)
[@@deriving show {with_path= false}]
