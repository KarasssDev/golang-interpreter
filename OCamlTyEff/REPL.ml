open Angstrom
open Printf
open Format
open Ocaml_typed_effects_lib.Ast
open Ocaml_typed_effects_lib.Check
open Ocaml_typed_effects_lib.Parser

(* let () = match parse_with pty "('a --> 'b -['e]-> 'c) --> 'a list --> 'b list -['e]-> 'c list" with
  | Ok ty -> pp_ty std_formatter ty
  | Error err -> printf "%s" err *)

let expr_s =
  {|
  let rec map : ('a -['e]-> 'b) --> 'a list -['e]-> 'b list = fun f: ('a -['e]-> 'b) -> fun xs : 'a list ->
    match xs with
    | [] -> []
    | x::xs -> (f x) :: (map f xs) in
  let id: 'a --> 'a = fun x: 'a -> x in
  map id
|}
;;

let expr_s =
  {|
  let rec map : ('a -['e]-> 'b) --> 'a list -['e]-> 'b list = fun f: ('a -['e]-> 'b) -> fun xs : 'a list ->
    match xs with
    | [] -> []
    | x::xs -> (f x) :: (map f xs) in
  map (fun n: int -> let o: () = println "hi" in n + 1)
|}
;;

let expr_s =
  {|
  let rec map2 : ('a --> 'b -['e]-> 'c) --> 'a list --> 'b list -['e, exc Exc1]-> 'c list = 
      fun f: ('a --> 'b -['e]-> 'c) ->
        fun l1: 'a list -> fun l2: 'b list ->
      match (l1, l2) with
      | ([], []) -> []
      | (a1::l1, a2::l2) -> let r: 'c = f a1 a2 in r :: map2 f l1 l2
      | (o1, o2) -> raiseExc1 ()
  in
  map2 
|}
;;

let expr_s =
  {|
  let rec map2 : ('a --> 'b -['e]-> 'c) --> 'a list --> 'b list -['e, exc Exc1]-> 'c list = 
      fun f: ('a --> 'b -['e]-> 'c) ->
        fun l1: 'a list -> fun l2: 'b list ->
      match (l1, l2) with
      | ([], []) -> []
      | (a1::l1, a2::l2) -> let r: 'c = f a1 a2 in r :: map2 f l1 l2
      | (o1, o2) -> raiseExc1 ()
  in
  map2 (fun n: int -> fun m: int -> n + m) (1 :: [])
|}
;;

let expr_s =
  {|
  let rec map2 : ('a --> 'b -['e]-> 'c) --> 'a list --> 'b list -['e, exc Exc1]-> 'c list = 
      fun f: ('a --> 'b -['e]-> 'c) ->
        fun l1: 'a list -> fun l2: 'b list ->
      match (l1, l2) with
      | ([], []) -> []
      | (a1::l1, a2::l2) -> let r: 'c = f a1 a2 in r :: map2 f l1 l2
      | (o1, o2) -> raiseExc1 ()
  in
  map2 (fun n: int -> fun m: 'a -> raiseExc1 ()) (1 :: [])
|}
;;

let expr_s =
  {|
  let rec map2 : ('a --> 'b -['e]-> 'c) --> 'a list --> 'b list -['e, exc Exc1]-> 'c list = 
      fun f: ('a --> 'b -['e]-> 'c) ->
        fun l1: 'a list -> fun l2: 'b list ->
      match (l1, l2) with
      | ([], []) -> []
      | (a1::l1, a2::l2) -> let r: 'c = f a1 a2 in r :: map2 f l1 l2
      | (o1, o2) -> raiseExc1 ()
  in
  map2 (fun n: int -> fun m: 'a -> raiseExc2 ()) (1 :: [])
|}
;;

let expr_s = {|
  let x: int ref = ref 1 in
  let o: () = x := !x + 1 in
  !x
|}

let expr_s = {|
  try raiseExc1 () with
  | Exc1 -> 1
|}

let expr_s = {|
  try raiseExc1 () with
  | Exc1 -> raiseExc2 ()
|}

let expr_s = {|
  try raiseExc1 () with
  | Exc1 -> raiseExc1 ()
|}

let expr_s = {|
  let f: bool -[exc Exc1, exc Exc2]-> string = fun flag: bool ->
    match flag with
    | true -> raiseExc1 ()
    | false -> raiseExc2 ()
  in
  try f true with
  | Exc1 -> raiseExc2 ()
  | Exc2 -> "literal"
|}

let expr_s = {|
  false || (1 + 3) * 2 + 10 >= 24 / 2 - 1 && 5 + 2 * 2 = 9
|}

(*  / 2 - 1 && 5 + 2 * 2 = 9 *)

let () =
  match parse_with pexpr expr_s with
  | Ok expr ->
    pp_expr std_formatter expr;
    let ty, effs =
      infer_tyeffs
        { decls =
            BindMap.of_seq
              (List.to_seq
                 [ "println", TFun (TString, EffSet.singleton EffIO, TTuple [])
                 ; ( "raiseExc1"
                   , TFun (TTuple [], EffSet.singleton (EffExc Exc1), TVar "bottom") )
                 ; ( "raiseExc2"
                   , TFun (TTuple [], EffSet.singleton (EffExc Exc2), TVar "bottom") )
                 ; "ref", TFun (TVar "a", EffSet.empty, TRef (TVar "a"))
                 ; "not", TFun (TBool, EffSet.empty, TBool)
                 ])
        ; btvars = BindSet.empty
        ; beffvars = BindSet.empty
        }
        expr
    in
    fprintf std_formatter "\n\n";
    pp_ty std_formatter ty;
    fprintf std_formatter "\n\n";
    pp_eff_set std_formatter effs;
    fprintf std_formatter "\n"
  | Error err -> Printf.printf "%s" err
;;

(* let expr_s =
  {|
  let rec map : ('a -['e]-> 'b) --> 'a list -['e]-> 'b list = fun f: ('a -['e]-> 'b) -> fun xs: 'a list ->
    match xs with
    | [] -> []
    | x::xs -> (f x) :: (map f xs) in
  
  let id : 'a --> 'a = fun x: 'a -> x in
  map (fun n: int -> let _: () = println "hi" in n + 1)
|}
;;

let expr_s1 = {|
  fun x: int -> x
|}

let expr_s15 = {|fun n: int -> let x: () = println "hi" in 1|}

let expr_s2 = {|
  let x: () = println "s" in 1
|}

let expr_s3 = {|
  let x: int --> int = fun n: int -> n in 1
|} *)

(* let () =
  pp_subst
    std_formatter
    (simple_subst
       (TTuple [ TVar "a"; TTuple [ TVar "a" ] ])
       (TTuple [ TTuple [ TVar "b" ]; TVar "b" ]))
;; *)

(* let () =
  match parse_with (pprogram) "
  let a: int = 1;;let rec main: int =
    try 0
    with | Exc1 -> match 0 with
    |1 -> let x: int = 2 in x
    |_ -> (fun y -> y) 2
  " with
  | Ok x ->
    pp_program std_formatter x;
    print_endline ""
  | Error e -> print_endline e
;; *)

(* let () =
  pp_subst
    std_formatter
    (simple_subst
       (TTuple [TFun(TVar "a", EffSet.of_list [EffVar "f"; EffIO], TVar "a"); TFun(TVar "a", EffSet.of_list [EffVar "f"], TVar "a")])
       (TTuple [TFun(TVar "x", EffSet.of_list [EffVar "e"], TVar "y"); TFun(TInt, EffSet.of_list [EffIO], TVar "x")])
    )
;; *)

(* let expr_s =
  {|
  let map : ('a -['e]-> 'b) --> 'a -['e]-> 'b  = fun f: ('a -['e]-> 'b) -> fun x: 'a -> f x in
  map
|}
;; *)

(* BindMap.fold
    (fun k v _ ->
      print_endline k;
      pp_ty std_formatter v;
      print_endline "")
    ty
    ();
  BindMap.fold
    (fun k v _ ->
      print_endline k;
      List.fold_right (fun e _ -> pp_eff std_formatter e) v ())
    eff
    () *)

let main =
  try 0 with
  | Not_found ->
    (match 0 with
    | 1 ->
      let x : int = 2 in
      x
    | _ -> (fun y -> y) 2)
;;
