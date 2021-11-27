open Ast
open Env

type exval =
  | IntV of int
  | BoolV of bool
  | StringV of string
  | TupleV of exval list
  | ListV of exval list

type env = exval Env.t

exception Tuple_compare

let rec match_pat pat var =
  match pat, var with
  | PWild, _ -> []
  | PVar name, v -> [ name, v ]
  | PTuple pats, TupleV vars when List.length pats = List.length vars ->
    List.fold_left2 (fun binds pat var -> binds @ match_pat pat var) [] pats vars
  | PList pats, TupleV vars when List.length pats = List.length vars ->
    List.fold_left2 (fun binds pat var -> binds @ match_pat pat var) [] pats vars
  | _ -> failwith "Interpretation error: Wrong match."
;;

let apply_infix_op op x y =
  match op, x, y with
  | Add, IntV x, IntV y -> IntV (x + y)
  | Sub, IntV x, IntV y -> IntV (x - y)
  | Mul, IntV x, IntV y -> IntV (x * y)
  | Div, IntV x, IntV y -> IntV (x / y)
  (* "<" block *)
  | Less, IntV x, IntV y -> BoolV (x < y)
  | Less, StringV x, StringV y -> BoolV (x < y)
  | Less, BoolV x, BoolV y -> BoolV (x < y)
  | Less, TupleV x, TupleV y when List.length x = List.length y -> BoolV (x < y)
  (* "<=" block *)
  | Leq, IntV x, IntV y -> BoolV (x <= y)
  | Leq, StringV x, StringV y -> BoolV (x <= y)
  | Leq, BoolV x, BoolV y -> BoolV (x <= y)
  | Leq, TupleV x, TupleV y when List.length x = List.length y -> BoolV (x <= y)
  (* ">" block *)
  | Gre, IntV x, IntV y -> BoolV (x > y)
  | Gre, StringV x, StringV y -> BoolV (x > y)
  | Gre, BoolV x, BoolV y -> BoolV (x > y)
  | Gre, TupleV x, TupleV y when List.length x = List.length y -> BoolV (x > y)
  (* ">=" block *)
  | Geq, IntV x, IntV y -> BoolV (x >= y)
  | Geq, StringV x, StringV y -> BoolV (x >= y)
  | Geq, BoolV x, BoolV y -> BoolV (x >= y)
  | Geq, TupleV x, TupleV y when List.length x = List.length y -> BoolV (x >= y)
  (* "=" block *)
  | Eq, IntV x, IntV y -> BoolV (x = y)
  | Eq, StringV x, StringV y -> BoolV (x = y)
  | Eq, BoolV x, BoolV y -> BoolV (x = y)
  | Eq, TupleV x, TupleV y -> BoolV (x = y)
  (* "!=" block *)
  | Neq, IntV x, IntV y -> BoolV (x != y)
  | Neq, StringV x, StringV y -> BoolV (x != y)
  | Neq, BoolV x, BoolV y -> BoolV (x != y)
  | Neq, TupleV x, TupleV y -> BoolV (x != y)
  (* Other bool ops *)
  | And, BoolV x, BoolV y -> BoolV (x && y)
  | Or, BoolV x, BoolV y -> BoolV (x || y)
  | _, TupleV x, TupleV y when List.length x != List.length y -> raise Tuple_compare
  | _ -> failwith "Interpretation error: Wrong infix operation."
;;

let apply_unary_op op x =
  match op, x with
  | Minus, IntV x -> IntV (-x)
  | Not, BoolV x -> BoolV (not x)
  | _ -> failwith "Interpretation error: Wrong unary operation."
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
  | EList exps -> ListV (List.map (eval_exp env) exps)
  | ETuple exps -> TupleV (List.map (eval_exp env) exps)
  | EIf (exp1, exp2, exp3) ->
    (match eval_exp env exp1 with
    | BoolV true -> eval_exp env exp2
    | BoolV false -> eval_exp env exp3
    | _ -> failwith "Interpretation error: couldn't interpret \"if\" expression")
  | ELet (bindings, exp1) ->
    let gen_env =
      List.fold_left
        (fun env binding ->
          match binding with
          | false, pat, exp ->
            let evaled = eval_exp env exp in
            let binds = match_pat pat evaled in
            List.fold_left (fun env (id, v) -> extend id v env) env binds
          | _ -> failwith "unimpl")
        env
        bindings
    in
    eval_exp gen_env exp1
  | _ -> failwith "Interpretation error: unimpl"
;;

let rec eval_dec env = function
  | DLet bindings ->
    (match bindings with
    | false, pat, exp ->
      let evaled = eval_exp env exp in
      let binds = match_pat pat evaled in
      let env = List.fold_left (fun env (id, v) -> extend id v env) env binds in
      env
    | _ -> failwith "Interpretation error: unimpl")
  | _ -> failwith "Interpretation error: unimpl"
;;

let str_converter = function
  | IntV x -> string_of_int x
  | BoolV x -> string_of_bool x
  | StringV x -> x
  | _ -> failwith "Interpretation error: not basic type."
;;

let exval_to_str = function
  | Some (IntV x) -> str_converter (IntV x)
  | Some (BoolV x) -> str_converter (BoolV x)
  | Some (StringV x) -> str_converter (StringV x)
  | None -> failwith "Interpretation error: what?"
  | Some (TupleV x) -> String.concat " " (List.map str_converter x)
  | Some (ListV x) -> String.concat " " (List.map str_converter x)
;;

let eval_test ast num =
  Printf.printf "Eval test %s\n" num;
  let evaled = eval_dec Env.empty ast in
  let env = evaled in
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
    Printf.printf "Interpretation error: Cannot compare tuples of different size.\n";
    true
;;

(* Eval test 5 *)
let%test _ =
  eval_test
    (DLet (false, PVar "x", ELet ([ false, PVar "y", EConst (CInt 5) ], EVar "y")))
    "5"
;;

(* Eval test 6 *)

(* let x =
    let y = 5 in
    let z = 10 in
    y + z
;; *)
let%test _ =
  eval_test
    (DLet
       ( false
       , PVar "x"
       , ELet
           ( [ false, PVar "y", EConst (CInt 5); false, PVar "z", EConst (CInt 10) ]
           , EOp (Add, EVar "y", EVar "z") ) ))
    "6"
;;

(* Eval test 7 *)

(* let x =
    let y = 5 in
    let y = 10 in
    y
;; *)
let%test _ =
  eval_test
    (DLet
       ( false
       , PVar "x"
       , ELet
           ( [ false, PVar "y", EConst (CInt 5); false, PVar "y", EConst (CInt 10) ]
           , EVar "y" ) ))
    "7"
;;

(* Eval test 8 *)

(* let x =
    let y =
      let y = 10 in
      5
    in
    y
;; *)
let%test _ =
  eval_test
    (DLet
       ( false
       , PVar "x"
       , ELet
           ( [ ( false
               , PVar "y"
               , ELet ([ false, PVar "y", EConst (CInt 10) ], EConst (CInt 5)) )
             ]
           , EVar "y" ) ))
    "8"
;;
