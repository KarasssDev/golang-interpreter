type c_types =
  | CT_INT
  | CT_CHAR
  | CT_STRUCT of string
  | CT_PTR of c_types
  | CT_ARRAY of int * c_types
  | CT_VOID
[@@deriving show { with_path = false }]

type c_args = CARGS of c_types * string
[@@deriving show { with_path = false }]

type c_values =
  | CINT of int
  | CCHAR of char
  | CARRAY of (int * c_values) list
  | CNULL
  | CVOID
[@@deriving show { with_path = false }]

type c_expr =
  | ADD of c_expr * c_expr
  | SUB of c_expr * c_expr
  | MUL of c_expr * c_expr
  | DIV of c_expr * c_expr
  | MOD of c_expr * c_expr
  | AND of c_expr * c_expr
  | OR of c_expr * c_expr
  | NOT of c_expr
  | EQUAL of c_expr * c_expr
  | NOT_EQUAL of c_expr * c_expr
  | GTE of c_expr * c_expr
  | GT of c_expr * c_expr
  | LTE of c_expr * c_expr
  | LT of c_expr * c_expr
  | LITERAL of c_values
  | FUNC_CALL of c_expr * c_expr list
  | VAR_NAME of string
  (* Pointer ops *)
  | DEREFERENCE of c_expr
  | ADDRESS of c_expr
  | INDEXER of string * c_expr
  | ACCESOR of c_expr * c_expr
  | INITIALIZER of c_expr list
  | EPOST_INCR of string * int
  | EPREF_INCR of string * int
  | EPOST_DECR of string * int
  | EPREF_DECR of string * int
[@@deriving show { with_path = false }]

type c_statements =
  | VAR_DECL of string * c_types * c_expr option
  | STRUCT_DECL of string * c_args list
  | EXPRESSION of c_expr
  | RETURN of c_expr
  | T_BLOCK of c_statements list
  | IF of c_expr * c_statements
  | IF_ELSE of c_expr * c_statements * c_statements
  | WHILE of c_expr * c_statements
  | FOR of c_statements * c_expr * c_statements * c_statements
  | STRUCT of string * c_args list
  | T_ASSIGN of c_expr * c_expr
  | ASSIGN_SUB of c_expr * c_expr
  | ASSIGN_ADD of c_expr * c_expr
  | ASSIGN_MUL of c_expr * c_expr
  | ASSIGN_DIV of c_expr * c_expr
  | ASSIGN_MOD of c_expr * c_expr
  | BREAK
  | CONTINUE
  | POST_INCR of c_expr
  | PREF_INCR of c_expr
  | POST_DECR of c_expr
  | PREF_DECR of c_expr
[@@deriving show { with_path = false }]

and c_prog =
  | C_PROG of c_prog list
  | C_INCLUDE of string list
  | TOP_STRUCT_DECL of string * c_args list
  | TOP_FUNC_DECL of c_types * string * c_args list * c_statements
  | TOP_VAR_DECL of string * c_types * c_expr option
[@@deriving show { with_path = false }]
