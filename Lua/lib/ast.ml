open Hashtbl_p

type arop = Sum | Sub | Mul | Div | FDiv | Mod
[@@deriving show {with_path = false}]

type logop = And | Or [@@deriving show {with_path = false}]
type unop = Not [@@deriving show {with_path = false}]

type relop = Eq | Neq | Le | Leq | Ge | Geq
[@@deriving show {with_path = false}]

type name = string [@@deriving show {with_path = false}]

type value =
  | VBool of bool
  | VNumber of float
  | VString of string
  | VTable of (value, value) Hashtbl_p.t
  (* name list -- function arguments, statement -- function body*)
  | VFunction of name list * statement
  | VNull
[@@deriving show {with_path = false}]

and if_stmt =
  | If of expr * statement
  | Elif of expr * statement
  | Else of statement

and expr =
  | Const of value
  | Var of name
  | ArOp of arop * expr * expr
  | LogOp of logop * expr * expr
  | UnOp of unop * expr
  | RelOp of relop * expr * expr
  (* name[expr1][expr2]...[], where 'name' is name of the table *)
  | TableAccess of name * expr list
  (* https://www.lua.org/pil/3.6.html *)
  | TableCreate of expr list
  (* name([expr list]), where 'name' is name of the function and 'expr list' is passed arguments*)
  | CallFunc of name * expr list
  | Assign of expr * expr
[@@deriving show {with_path = false}]

and statement =
  (* https://www.lua.org/pil/4.3.1.html *)
  (* if * elseif list * [else]  *)
  | IfStatement of
      (expr * statement) * (expr * statement) list * statement option
  (* while expr do statement end *)
  | While of expr * statement
  (* for i = 1, 5, 2 do ... end *)
  (* name -- loop variable; expr list -- 'from', 'to', ['step']; statement -- loop body *)
  | ForNumerical of name * expr list * statement
  | Break
  (* https://www.lua.org/pil/4.2.html *)
  | Local of statement
  | Return of expr
  (* x, y, t[1] = true, false *)
  | VarDec of (expr * expr) list
  | Expression of expr
  | Block of statement list
  (* name -- name of function, name list -- function arguments, statement -- function body*)
  | FuncDec of name * name list * statement
[@@deriving show {with_path = false}]
