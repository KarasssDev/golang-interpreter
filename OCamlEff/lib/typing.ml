type binder = int [@@deriving show { with_path = false }]

module VarSet = struct
  include Caml.Set.Make (Int)

  let pp ppf s =
    Format.fprintf ppf "[ ";
    iter (Format.fprintf ppf "%d; ") s;
    Format.fprintf ppf "]"
  ;;
end

type binder_set = VarSet.t [@@deriving show { with_path = false }]

type type_exp =
  | TPrim of string
  | TVar of binder
  | TTuple of type_exp list
  | TList of type_exp
  | TArrow of type_exp * type_exp
[@@deriving show { with_path = false }]

type scheme = S of binder_set * type_exp [@@deriving show { with_path = false }]

let arrow l r = TArrow (l, r)
let int_type = TPrim "int"
let bool_type = TPrim "bool"
let unit_type = TPrim "unit"
let string_type = TPrim "string"
