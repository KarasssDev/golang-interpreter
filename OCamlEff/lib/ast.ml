type name = string

type value = 
  | ValInt of int
  | ValChar of char
  | ValString of string
  | ValBool of bool
  | ValUnit of unit
  | ValList of value list
  (* | ValFunc of name list * statement *)

and expr = 
  | Const of value
  | Var of name

and statement = 
  | LetBinding of expr * expr
