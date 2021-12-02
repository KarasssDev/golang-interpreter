open Ast

module IdMap = Map.Make (struct
  type t = id

  let compare = compare
end)

type 'a id_t = 'a IdMap.t

module EffMap = Map.Make (struct
  type t = id

  let compare = compare
end)

type 'a eff_t = 'a EffMap.t

exception Not_bound

let empty_id_map = IdMap.empty
let empty_eff_map = EffMap.empty
let extend_id_map id x = IdMap.add id x
let extend_eff_map id x = EffMap.add id x

let lookup_id_map id env =
  try IdMap.find id env with
  | Not_found -> raise Not_bound
;;

let lookup_eff_map id context =
  try EffMap.find id context with
  | Not_found -> raise Not_bound
;;
