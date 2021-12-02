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

type tyexp =
  | TWild                   (*  _                       *)
  | TInt                    (*  int                     *)
  | TString                 (*  string                  *)
  | TBool                   (*  bool                    *)
  | TVar of binder          (*  1 (polymorphic type)    *)
  | TTuple of tyexp list    (*  int * string            *)
  | TList of tyexp          (*  string list list        *)
  | TArrow of tyexp * tyexp (*  int -> string           *)
[@@deriving show { with_path = false }]

type scheme = S of binder_set * tyexp [@@deriving show { with_path = false }]
