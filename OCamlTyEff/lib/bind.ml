module BindMap = Map.Make (String)
module BindSet = Set.Make (String)

exception Not_bound of string

let find_bind map name =
  try BindMap.find name map with
  | Not_found -> raise (Not_bound name)
;;

let is_bound set name =
  try
    let _ = BindSet.find set name in
    true
  with
  | Not_found -> false
;;

let is_not_bound set name = not (is_bound set name)

let pp_bind_map pp fmt map =
  BindMap.iter (fun k v -> Format.fprintf fmt "%s=%a\n" k pp v) map
;;
