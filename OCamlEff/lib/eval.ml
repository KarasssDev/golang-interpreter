open Ast
open Env

type exval =
  | IntV of int
  | BoolV of bool
  | StringV of string
  | TupleV of exval list
  | ListV of exval list
  | FunV of pat * exp * exval Env.t

type env = exval Env.t

exception Tuple_compare

let rec match_pat pat var =
  match pat, var with
  | PWild, _ -> []
  | PVar name, v -> [ name, v ]
  | PCons (pat1, pat2), ListV vars ->
    (match vars with
    | [ hd; tl ] -> match_pat pat1 hd @ match_pat pat2 tl
    | _ -> failwith "Interpretation error: Wrong match.")
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
  | ECons (exp1, exp2) ->
    let exp1_evaled = eval_exp env exp1 in
    let exp2_evaled = eval_exp env exp2 in
    (match exp2_evaled with
    | ListV list -> ListV ([ exp1_evaled ] @ list)
    | x -> ListV [ exp1_evaled; x ])
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
          (* Think of let and let rec *)
          | _, pat, exp ->
            let evaled = eval_exp env exp in
            let binds = match_pat pat evaled in
            List.fold_left (fun env (id, v) -> extend id v env) env binds)
        env
        bindings
    in
    eval_exp gen_env exp1
  | EFun (pat, exp) -> FunV (pat, exp, env)
  | EApp (exp1, exp2) ->
    (match eval_exp env exp1 with
    | FunV (pat, exp, fenv) ->
      let binds = match_pat pat (eval_exp env exp2) in
      let env = List.fold_left (fun env (id, v) -> extend id v env) fenv binds in
      eval_exp env exp
    | _ -> failwith "Interpretation error: wrong application")
  | _ -> failwith "Interpretation error: unimpl"
;;

let eval_dec env = function
  | DLet bindings ->
    (match bindings with
    (* Think of let and let rec *)
    | _, pat, exp ->
      let evaled = eval_exp env exp in
      let binds = match_pat pat evaled in
      let env = List.fold_left (fun env (id, v) -> extend id v env) env binds in
      env)
  | _ -> failwith "Interpretation error: unimpl"
;;

let str_converter = function
  | IntV x -> string_of_int x
  | BoolV x -> string_of_bool x
  | StringV x -> x
  | _ -> failwith "Interpretation error: not basic type."
;;

let exval_to_str = function
  | IntV x -> str_converter (IntV x)
  | BoolV x -> str_converter (BoolV x)
  | StringV x -> str_converter (StringV x)
  | TupleV x -> String.concat " " (List.map str_converter x)
  | ListV x -> String.concat " " (List.map str_converter x)
  | FunV (pat, _, _) ->
    (match pat with
    | PVar x -> x
    | _ -> "error")
;;

type decls = decl list

let eval_test decls expected =
  try
    let init_env = Env.empty in
    let env =
      List.fold_left
        (fun env decl ->
          let new_env = eval_dec env decl in
          new_env)
        init_env
        decls
    in
    let res =
      IdMap.fold
        (fun k v ln ->
          let new_res = ln ^ Printf.sprintf "%s -> %s " k (exval_to_str !v) in
          new_res)
        env
        ""
    in
    if res = expected then true else false
  with
  | Tuple_compare ->
    if expected = "Interpretation error: Cannot compare tuples of different size."
    then true
    else false
;;

(* Eval test 1 *)

(* 
  let x = 1
*)
let%test _ = eval_test [ DLet (false, PVar "x", EConst (CInt 1)) ] "x -> 1 "

(* Eval test 2 *)

(* 
  let (x, y) = (1, 2)
*)
let%test _ =
  eval_test
    [ DLet
        (false, PTuple [ PVar "x"; PVar "y" ], ETuple [ EConst (CInt 1); EConst (CInt 2) ])
    ]
    "x -> 1 y -> 2 "
;;

(* Eval test 3 *)

(* 
  let x = 3 < 2
*)
let%test _ =
  eval_test
    [ DLet (false, PVar "x", EOp (Less, EConst (CInt 3), EConst (CInt 2))) ]
    "x -> false "
;;

(* Eval test 4 *)

(* 
  let x = (1, 2) < (1, 2, 3)
*)
let%test _ =
  eval_test
    [ DLet
        ( false
        , PVar "x"
        , EOp
            ( Less
            , ETuple [ EConst (CInt 1); EConst (CInt 2) ]
            , ETuple [ EConst (CInt 1); EConst (CInt 2); EConst (CInt 3) ] ) )
    ]
    "Interpretation error: Cannot compare tuples of different size."
;;

(* Eval test 5 *)

(* 
  let x =
    let y = 5
    in y
*)
let%test _ =
  eval_test
    [ DLet (false, PVar "x", ELet ([ false, PVar "y", EConst (CInt 5) ], EVar "y")) ]
    "x -> 5 "
;;

(* Eval test 6 *)

(* 
  let x =
    let y = 5 in
    let z = 10 in
    y + z
*)
let%test _ =
  eval_test
    [ DLet
        ( false
        , PVar "x"
        , ELet
            ( [ false, PVar "y", EConst (CInt 5); false, PVar "z", EConst (CInt 10) ]
            , EOp (Add, EVar "y", EVar "z") ) )
    ]
    "x -> 15 "
;;

(* Eval test 7 *)

(* 
  let x =
    let y = 5 in
    let y = 10 in
    y
*)
let%test _ =
  eval_test
    [ DLet
        ( false
        , PVar "x"
        , ELet
            ( [ false, PVar "y", EConst (CInt 5); false, PVar "y", EConst (CInt 10) ]
            , EVar "y" ) )
    ]
    "x -> 10 "
;;

(* Eval test 8 *)

(* 
  let x =
    let y =
      let y = 10 in
      5
    in
    y
*)
let%test _ =
  eval_test
    [ DLet
        ( false
        , PVar "x"
        , ELet
            ( [ ( false
                , PVar "y"
                , ELet ([ false, PVar "y", EConst (CInt 10) ], EConst (CInt 5)) )
              ]
            , EVar "y" ) )
    ]
    "x -> 5 "
;;

(* Eval test 9 *)

(* 
  let f x y = x + y
*)
let%test _ =
  eval_test
    [ DLet
        (false, PVar "f", EFun (PVar "x", EFun (PVar "y", EOp (Add, EVar "x", EVar "y"))))
    ]
    "f -> x "
;;

(* Eval test 10 *)

(* 
  let f x y = x + y
  let a = f 1 2 
*)
let%test _ =
  eval_test
    [ DLet
        (false, PVar "f", EFun (PVar "x", EFun (PVar "y", EOp (Add, EVar "x", EVar "y"))))
    ; DLet (false, PVar "a", EApp (EApp (EVar "f", EConst (CInt 1)), EConst (CInt 2)))
    ]
    "a -> 3 f -> x "
;;

(* Eval test 11 *)

(* 
let f x y = x + y
let kek = f 1
let lol = kek 2 
*)
let%test _ =
  eval_test
    [ DLet
        (false, PVar "f", EFun (PVar "x", EFun (PVar "y", EOp (Add, EVar "x", EVar "y"))))
    ; DLet (false, PVar "kek", EApp (EVar "f", EConst (CInt 1)))
    ; DLet (false, PVar "lol", EApp (EVar "kek", EConst (CInt 2)))
    ]
    "f -> x kek -> y lol -> 3 "
;;
