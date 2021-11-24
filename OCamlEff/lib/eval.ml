open Ast
open Env

type exval =
  | UnitV
  | IntV of int
  | BoolV of bool
  | StringV of string

type env = exval Env.t

let rec match_pat pat var =
  match pat, var with
  | PWild, _ -> []
  | PVar name, v -> [ name, v ]
  | (PConst _ | PList _ | PTuple _), _ -> []
;;

let apply_op op x y =
  match op, x, y with
  | Add, IntV x, IntV y -> IntV (x + y)
  | Sub, IntV x, IntV y -> IntV (x - y)
  | Mul, IntV x, IntV y -> IntV (x * y)
  | Div, IntV x, IntV y -> IntV (x / y)
  | _ -> failwith "unimpl"
;;

(*Add other ops later*)
let rec eval_exp env = function
  | EConst x ->
    (match x with
    | CInt x -> IntV x
    | CBool x -> BoolV x
    | CString x -> StringV x)
  | EVar x ->
    (try Env.lookup x env with
    | Env.Not_bound -> assert false)
  | EOp (op, x, y) ->
    let exp_x = eval_exp env x in
    let exp_y = eval_exp env y in
    apply_op op exp_x exp_y
  | _ -> failwith "unimpl"
;;

let rec eval_dec env = function
  | DLet binding ->
    (match binding with
    | false, pat, exp ->
      let evaled = eval_exp env exp in
      let binds = match_pat pat evaled in
      let env = List.fold_left (fun env (id, v) -> extend id v env) env binds in
      binds, env
    | _ -> failwith "unimpl")
  | _ -> failwith "unimpl"
;;

let exval_to_str = function
  | Some (IntV x) -> string_of_int x
  | Some (BoolV x) -> string_of_bool x
  | Some (StringV x) -> x
  | Some UnitV -> "unit"
  | None -> failwith "what?"
;;

let eval_test ast =
  let evaled = eval_dec Env.empty ast in
  let _, env = evaled in
  IdMap.iter (fun k v -> Printf.printf "%s -> %s\n" k (exval_to_str !v)) env;
  true
;;

let%test _ = eval_test (DLet (false, PVar "x", EConst (CInt 1)))
