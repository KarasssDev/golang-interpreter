open Ast

module IdMap = Map.Make (struct
  type t = id

  let compare = compare
end)

type 'a t = 'a IdMap.t

exception Not_bound

let empty = IdMap.empty
let extend id x = IdMap.add id x

let lookup id env =
  try IdMap.find id env with
  | Not_found -> raise Not_bound
;;
