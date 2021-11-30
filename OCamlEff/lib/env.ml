open Ast

module IdMap = Map.Make (struct
  type t = id

  let compare = compare
end)

type 'a t = 'a option ref IdMap.t

exception Not_bound
exception Not_ready
exception Map_corrupted

let empty = IdMap.empty
let extend id x = IdMap.add id (ref (Some x))

let lookup id env =
  let helper =
    try IdMap.find id env with
    | Not_found -> raise Not_bound
  in
  match !helper with
  | Some x -> x
  | None -> raise Not_ready
;;

let reserve id = IdMap.add id (ref None)

let emplace id x env =
  let r =
    try IdMap.find id env with
    | Not_found -> raise Not_found
  in
  match !r with
  | None -> r := Some x
  | Some _ -> raise Map_corrupted
;;
