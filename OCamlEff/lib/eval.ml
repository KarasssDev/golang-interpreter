open Ast
open Env

type exval =
  | IntV of int
  | BoolV of bool
  | StringV of string
  | TupleV of exval list

type env = exval Env.t

exception Tuple_compare

let rec match_pat pat var =
  match pat, var with
  | PWild, _ -> []
  | PVar name, v -> [ name, v ]
  | PTuple pats, TupleV vars when List.length pats = List.length vars ->
    List.fold_left2 (fun binds pat var -> binds @ match_pat pat var) [] pats vars
  | _ -> failwith "unimpl"
;;

let apply_infix_op op x y =
  match op, x, y with
  | Add, IntV x, IntV y -> IntV (x + y)
  | Sub, IntV x, IntV y -> IntV (x - y)
  | Mul, IntV x, IntV y -> IntV (x * y)
  | Div, IntV x, IntV y -> IntV (x / y)
  | Less, IntV x, IntV y -> BoolV (x < y)
  | Less, StringV x, StringV y -> BoolV (x < y)
  | Less, BoolV x, BoolV y -> BoolV (x < y)
  | Less, TupleV x, TupleV y when List.length x = List.length y -> BoolV (x < y)
  | Leq, IntV x, IntV y -> BoolV (x <= y)
  | Leq, StringV x, StringV y -> BoolV (x <= y)
  | Leq, BoolV x, BoolV y -> BoolV (x <= y)
  | Leq, TupleV x, TupleV y when List.length x = List.length y -> BoolV (x <= y)
  | Gre, IntV x, IntV y -> BoolV (x > y)
  | Gre, StringV x, StringV y -> BoolV (x > y)
  | Gre, BoolV x, BoolV y -> BoolV (x > y)
  | Gre, TupleV x, TupleV y when List.length x = List.length y -> BoolV (x > y)
  | Geq, IntV x, IntV y -> BoolV (x >= y)
  | Geq, StringV x, StringV y -> BoolV (x >= y)
  | Geq, BoolV x, BoolV y -> BoolV (x >= y)
  | Geq, TupleV x, TupleV y when List.length x = List.length y -> BoolV (x >= y)
  | Eq, IntV x, IntV y -> BoolV (x = y)
  | Eq, StringV x, StringV y -> BoolV (x = y)
  | Eq, BoolV x, BoolV y -> BoolV (x = y)
  | Eq, TupleV x, TupleV y -> BoolV (x = y)
  | Neq, IntV x, IntV y -> BoolV (x != y)
  | Neq, StringV x, StringV y -> BoolV (x != y)
  | Neq, BoolV x, BoolV y -> BoolV (x != y)
  | Neq, TupleV x, TupleV y -> BoolV (x != y)
  | And, BoolV x, BoolV y -> BoolV (x && y)
  | Or, BoolV x, BoolV y -> BoolV (x && y)
  | _, TupleV x, TupleV y when List.length x != List.length y -> raise Tuple_compare
  | _ -> failwith "Wrong infix operation."
;;

let apply_unary_op op x =
  match op, x with
  | Minus, IntV x -> IntV (-x)
  | Not, BoolV x -> BoolV (not x)
  | _ -> failwith "Wrong unary operation."
;;

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
    apply_infix_op op exp_x exp_y
  | EUnOp (op, x) ->
    let exp_x = eval_exp env x in
    apply_unary_op op exp_x
  | ETuple exps -> TupleV (List.map (eval_exp env) exps)
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

let str_converter = function
  | IntV x -> string_of_int x
  | BoolV x -> string_of_bool x
  | StringV x -> x
  | _ -> failwith "not basic type"
;;

let exval_to_str = function
  | Some (IntV x) -> str_converter (IntV x)
  | Some (BoolV x) -> str_converter (BoolV x)
  | Some (StringV x) -> str_converter (StringV x)
  | None -> failwith "what?"
  | Some (TupleV x) -> String.concat " " (List.map str_converter x)
;;

let eval_test ast num =
  Printf.printf "Eval test %s\n" num;
  let evaled = eval_dec Env.empty ast in
  let _, env = evaled in
  IdMap.iter (fun k v -> Printf.printf "%s -> %s\n" k (exval_to_str !v)) env;
  true
;;

(* Eval test 1 *)
let%test _ = eval_test (DLet (false, PVar "x", EConst (CInt 1))) "1"

(* Eval test 2 *)
let%test _ =
  eval_test
    (DLet
       (false, PTuple [ PVar "x"; PVar "y" ], ETuple [ EConst (CInt 1); EConst (CInt 2) ]))
    "2"
;;

(* Eval test 3 *)
let%test _ =
  eval_test (DLet (false, PVar "x", EOp (Less, EConst (CInt 3), EConst (CInt 2)))) "3"
;;

(* Eval test 4 *)
let%test _ =
  try
    eval_test
      (DLet
         ( false
         , PVar "x"
         , EOp
             ( Less
             , ETuple [ EConst (CInt 1); EConst (CInt 2) ]
             , ETuple [ EConst (CInt 1); EConst (CInt 2); EConst (CInt 3) ] ) ))
      "4"
  with
  | Tuple_compare ->
    Printf.printf "Cannot compare tuples of different size.";
    true
;;
