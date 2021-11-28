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
  | TInt
  | TSring
  | TBool
  | TVar of binder
  | TTuple of tyexp list
  | TList of tyexp
  | TArrow of tyexp * tyexp
[@@deriving show { with_path = false }]

type scheme = S of binder_set * tyexp [@@deriving show { with_path = false }]

