type types =
  | CT_INT
  | CT_CHAR
  | CT_STRUCT of string
  | CT_PTR of types
  | CT_ARRAY of int * types  (**size and type of array*)
  | CT_VOID
[@@deriving show { with_path = false }]

type args = CARGS of types * string [@@deriving show { with_path = false }]

type values =
  | CINT of int
  | CCHAR of char
  | CARRAY of expr list  (**array of indexed values in array*)
  | CNULL
  | CVOID
[@@deriving show { with_path = false }]

and expr =
  | ADD of expr * expr
  | SUB of expr * expr
  | MUL of expr * expr
  | DIV of expr * expr
  | MOD of expr * expr
  | AND of expr * expr
  | OR of expr * expr
  | NOT of expr
  | EQUAL of expr * expr
  | NOT_EQUAL of expr * expr
  | GTE of expr * expr
  | GT of expr * expr
  | LTE of expr * expr
  | LT of expr * expr
  | LITERAL of values
  | FUNC_CALL of string * expr list
  | VAR_NAME of string
  | INDEXER of string * expr  (** ~ name\[expr\] *)
  | ACCESOR of expr * expr  (** ~ expr.expr *)
  | INITIALIZER of expr list
      (** Initilizer for structures and arrays. For example: ct_name name = \{arg1, arg2\}, then INITIALIZER ~ \{arg1, arg2\}*)
  | TYPE of types  (** For example: sizeof(int), then TYPE ~ int *)
  | DEREFERENCE of expr  (** ~ *expr *)
  | ADDRESS of expr  (** ~ &expr *)
[@@deriving show { with_path = false }]

type statements =
  | VAR_DECL of string * types * expr option
  | EXPRESSION of expr
  | RETURN of expr
  | BLOCK of statements list
  | IF of expr * statements
  | IF_ELSE of expr * statements * statements
  | WHILE of expr * statements
  | FOR of (statements option) * (expr option) * (statements option) * statements
  | ASSIGN of expr * expr
  | ASSIGN_SUB of expr * expr
  | ASSIGN_ADD of expr * expr
  | ASSIGN_MUL of expr * expr
  | ASSIGN_DIV of expr * expr
  | ASSIGN_MOD of expr * expr
  
  | BREAK
  | CONTINUE
[@@deriving show { with_path = false }]

and prog =
  | C_PROG of prog list
  | C_INCLUDE of string list
  | TOP_STRUCT_DECL of string * args list
  | TOP_FUNC_DECL of types * string * args list * statements
  | TOP_VAR_DECL of string * types * expr option
[@@deriving show { with_path = false }]

module Hashtbl = struct
  include Hashtbl
  
  let pp pp_key pp_value ppf  values =
    Hashtbl.iter (fun key data ->
      Format.fprintf ppf "@[<1>%a: %a@]@." pp_key key pp_value data)
        values
end 