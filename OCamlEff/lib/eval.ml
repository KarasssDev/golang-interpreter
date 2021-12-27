open Ast
open Env
open Format

(* module type MONAD_FAIL = sig
  include Base.Monad.S2

  val fail : 'err -> ('a, 'err) t
end *)

type state =
  { env: exval Env.id_t
  ; context: effhval Env.eff_t
  }

and effhval = EffHV of pat * ident * exp

and exval =
  | IntV of int
  | BoolV of bool
  | StringV of string
  | TupleV of exval list
  | ListV of exval list
  | FunV of pat * exp * state
  | Eff1V of capitalized_ident
  | Eff2V of capitalized_ident * exval
  | EffDec1V of capitalized_ident * tyexp
  | EffDec2V of capitalized_ident * tyexp * tyexp
  | ContV of ident

type error =
  | Match_fail of pat * exval
  | Tuple_compare of exval * exval
  | No_handler of capitalized_ident
  | No_effect of capitalized_ident
  | Wrong_infix_op of infix_op * exval * exval
  | Wrong_unary_op of unary_op * exval
  | Undef_var of ident
  | Interp_error of exp
  | Match_exhaust of exp
  | Not_cont_val of ident
  | Not_bound

module R : sig
  open Base

  type 'a t

  val bind : 'a t -> f:('a -> 'b t) -> 'b t
  val return : 'a -> 'a t
  val fail : error -> 'a t

  include Monad.Infix with type 'a t := 'a t

  module Syntax : sig
    val ( let* ) : 'a t -> ('a -> 'b t) -> 'b t
  end

  (** Running a transformer: getting the inner result value *)
  val run : 'a t -> ('a, error) Result.t
end = struct
  (* A compositon: State monad after Result monad *)
  type 'a t = int -> int * ('a, error) Result.t

  let ( >>= ) : 'a 'b. 'a t -> ('a -> 'b t) -> 'b t =
   fun m f st ->
    let last, r = m st in
    match r with
    | Result.Error x -> last, Error x
    | Ok a -> f a last
 ;;

  let fail e st = st, Result.error e
  let return x last = last, Result.ok x
  let bind x ~f = x >>= f

  let ( >>| ) : 'a 'b. 'a t -> ('a -> 'b) -> 'b t =
   fun x f st ->
    match x st with
    | st, Ok x -> st, Ok (f x)
    | st, Result.Error e -> st, Result.Error e
 ;;

  module Syntax = struct
    let ( let* ) x f = bind x ~f
  end

  let run m = snd (m 0)
end

module Interpret = struct
  open R
  open Syntax

  let fold list ~f ~init =
    let rec helper acc = function
      | [] -> acc
      | hd :: tl -> helper (acc >>= fun acc -> f acc hd) tl
    in
    helper (return init) list
  ;;

  let create_state () = { env = Env.IdMap.empty; context = Env.EffMap.empty }

  let lookup_in_env id state =
    try return (lookup_id_map id state.env) with
    | Not_bound -> fail Not_bound
  ;;

  let lookup_in_context id state =
    try return (lookup_eff_map id state.context) with
    | Not_bound -> fail Not_bound
  ;;

  let extend_env id v state = { state with env = extend_id_map id v state.env }

  let extend_context id v state =
    { state with context = extend_eff_map id v state.context }
  ;;

  let rec match_pat pat var =
    match pat, var with
    | PWild, _ -> return []
    | PVar name, v -> return [ name, v ]
    | PConst x, v ->
      (match x, v with
      | CInt a, IntV b when a = b -> return []
      | CString a, StringV b when a == b -> return []
      | CBool a, BoolV b when a == b -> return []
      | _ -> fail (Match_fail (PConst x, v)))
    | PCons (pat1, pat2), ListV (hd :: tl) ->
      let* hd_matched = match_pat pat1 hd in
      let* tl_matched = match_pat pat2 (ListV tl) in
      return (hd_matched @ tl_matched)
    | PNil, ListV [] -> return []
    | PTuple pats, TupleV vars ->
      (match pats, vars with
      | hd_p :: tl_p, hd_v :: tl_v ->
        let* bind_hd = match_pat hd_p hd_v in
        let* bind_tl = match_pat (PTuple tl_p) (TupleV tl_v) in
        return (bind_hd @ bind_tl)
      | [], [] -> return []
      | _ -> fail (Match_fail (PTuple pats, TupleV vars)))
    | PEffect1 name_p, Eff1V name_exp when name_p == name_exp -> return []
    | PEffect2 (name_p, p), Eff2V (name_exp, v) when name_p == name_exp -> match_pat p v
    | PEffectH (pat, _), Eff1V name_exp -> match_pat pat (Eff1V name_exp)
    | PEffectH (pat, _), Eff2V (name_exp, v) -> match_pat pat (Eff2V (name_exp, v))
    | a, b -> fail (Match_fail (a, b))
  ;;

  let apply_infix_op op x y =
    match op, x, y with
    | Add, IntV x, IntV y -> return (IntV (x + y))
    | Sub, IntV x, IntV y -> return (IntV (x - y))
    | Mul, IntV x, IntV y -> return (IntV (x * y))
    | Div, IntV x, IntV y -> return (IntV (x / y))
    (* "<" block *)
    | Less, IntV x, IntV y -> return (BoolV (x < y))
    | Less, StringV x, StringV y -> return (BoolV String.(x < y))
    | Less, TupleV x, TupleV y when List.length x = List.length y ->
      return (BoolV (x < y))
    | Less, ListV x, ListV y -> return (BoolV (x < y))
    (* "<=" block *)
    | Leq, IntV x, IntV y -> return (BoolV (x <= y))
    | Leq, StringV x, StringV y -> return (BoolV (x <= y))
    | Leq, TupleV x, TupleV y when List.length x = List.length y ->
      return (BoolV (x <= y))
    | Leq, ListV x, ListV y -> return (BoolV (x <= y))
    (* ">" block *)
    | Gre, IntV x, IntV y -> return (BoolV (x > y))
    | Gre, StringV x, StringV y -> return (BoolV (x > y))
    | Gre, TupleV x, TupleV y when List.length x = List.length y -> return (BoolV (x > y))
    | Gre, ListV x, ListV y -> return (BoolV (x > y))
    (* ">=" block *)
    | Geq, IntV x, IntV y -> return (BoolV (x >= y))
    | Geq, StringV x, StringV y -> return (BoolV (x >= y))
    | Geq, TupleV x, TupleV y when List.length x = List.length y ->
      return (BoolV (x >= y))
    | Geq, ListV x, ListV y -> return (BoolV (x >= y))
    (* "=" block *)
    | Eq, IntV x, IntV y -> return (BoolV (x == y))
    | Eq, StringV x, StringV y -> return (BoolV (x == y))
    | Eq, BoolV x, BoolV y -> return (BoolV (x == y))
    | Eq, TupleV x, TupleV y -> return (BoolV (x == y))
    | Eq, ListV x, ListV y -> return (BoolV (x == y))
    (* "!=" block *)
    | Neq, IntV x, IntV y -> return (BoolV (x != y))
    | Neq, StringV x, StringV y -> return (BoolV (x != y))
    | Neq, BoolV x, BoolV y -> return (BoolV (x != y))
    | Neq, TupleV x, TupleV y -> return (BoolV (x != y))
    | Neq, ListV x, ListV y -> return (BoolV (x != y))
    (* Other bool ops *)
    | And, BoolV x, BoolV y -> return (BoolV (x && y))
    | Or, BoolV x, BoolV y -> return (BoolV (x || y))
    (* failures *)
    | _, TupleV x, TupleV y when List.length x != List.length y ->
      fail (Tuple_compare (TupleV x, TupleV y))
    | a, b, c -> fail (Wrong_infix_op (a, b, c))
  ;;

  let apply_unary_op op x =
    match op, x with
    | Minus, IntV x -> return (IntV (-x))
    | Not, BoolV x -> return (BoolV (not x))
    | a, b -> fail (Wrong_unary_op (a, b))
  ;;

  let rec scan_cases = function
    | hd :: tl ->
      (match hd with
      | PEffectH (PEffect1 name, cont), exp ->
        (name, EffHV (PEffect1 name, cont, exp)) :: scan_cases tl
      | PEffectH (PEffect2 (name, pat), cont), exp ->
        (name, EffHV (PEffect2 (name, pat), cont, exp)) :: scan_cases tl
      | _ -> scan_cases tl)
    | [] -> []
  ;;

  let rec eval_exp state = function
    | ENil -> return (ListV [])
    | EConst x ->
      (match x with
      | CInt x -> return (IntV x)
      | CBool x -> return (BoolV x)
      | CString x -> return (StringV x))
    | EVar x ->
      (match Result.map (fun t -> t) (run (lookup_in_env x state)) with
      | Ok b -> return b
      | Error _ -> fail (Undef_var x))
    | EOp (op, x, y) ->
      let* exp_x = eval_exp state x in
      let* exp_y = eval_exp state y in
      apply_infix_op op exp_x exp_y
    | EUnOp (op, x) ->
      let* exp_x = eval_exp state x in
      apply_unary_op op exp_x
    | ETuple exps ->
      (match exps with
      | hd :: tl ->
        let* hd_evaled = eval_exp state hd in
        let* tl_evaled = eval_exp state (ETuple tl) in
        (match tl_evaled with
        | TupleV exvals -> return (TupleV (hd_evaled :: exvals))
        | _ -> fail (Interp_error (ETuple exps)))
      | [] -> return (TupleV []))
    | ECons (exp1, exp2) ->
      let* exp1_evaled = eval_exp state exp1 in
      let* exp2_evaled = eval_exp state exp2 in
      (match exp2_evaled with
      | ListV list -> return (ListV (exp1_evaled :: list))
      | x -> return (ListV [ exp1_evaled; x ]))
    | EIf (exp1, exp2, exp3) ->
      let* evaled = eval_exp state exp1 in
      (match evaled with
      | BoolV true -> eval_exp state exp2
      | BoolV false -> eval_exp state exp3
      | _ -> fail (Interp_error (EIf (exp1, exp2, exp3))))
    | ELet (bindings, exp1) ->
      let gen_state =
        fold bindings ~init:state ~f:(fun state binding ->
            let _, pat, exp = binding in
            let* evaled = eval_exp state exp in
            let* binds = match_pat pat evaled in
            fold binds ~init:state ~f:(fun state (id, v) ->
                return @@ extend_env id v state))
      in
      let* s = gen_state in
      eval_exp s exp1
    | EFun (pat, exp) -> return (FunV (pat, exp, state))
    | EApp (exp1, exp2) ->
      let* evaled = eval_exp state exp1 in
      (match evaled with
      | FunV (pat, exp, fstate) ->
        let* evaled2 = eval_exp state exp2 in
        let* binds = match_pat pat evaled2 in
        let new_state =
          List.fold_left (fun state (id, v) -> extend_env id v state) fstate binds
        in
        let very_new_state =
          match exp1 with
          | EVar x -> extend_env x evaled new_state
          | _ -> new_state
        in
        eval_exp { very_new_state with context = state.context } exp
      | _ -> fail (Interp_error (EApp (exp1, exp2))))
    | EMatch (exp, mathchings) ->
      let effh = scan_cases mathchings in
      let exp_state =
        List.fold_left (fun state (id, v) -> extend_context id v state) state effh
      in
      let* evaled = eval_exp exp_state exp in
      let rec do_match = function
        | [] -> fail (Match_exhaust (EMatch (exp, mathchings)))
        | (pat, exp) :: tl ->
          (match Result.map (fun t -> t) (run (match_pat pat evaled)) with
          | Ok binds ->
            let state =
              List.fold_left (fun state (id, v) -> extend_env id v state) state binds
            in
            eval_exp state exp
          | Error _ -> do_match tl)
      in
      do_match mathchings
    | EPerform exp ->
      let* eff = eval_exp state exp in
      (match eff with
      | Eff1V name ->
        let lookup = lookup_in_context name state in
        (match Result.map (fun t -> t) (run lookup) with
        | Error _ -> fail (No_handler name)
        | Ok (EffHV (pat, cont_val, exph)) ->
          (match Result.map (fun t -> t) (run (lookup_in_env name state)) with
          | Error _ -> fail (No_effect name)
          | Ok _ ->
            let _ = match_pat pat (Eff1V name) in
            eval_exp (extend_env cont_val (ContV cont_val) state) exph))
      | Eff2V (name, exval) ->
        let lookup = lookup_in_context name state in
        (match Result.map (fun t -> t) (run lookup) with
        | Error _ -> fail (No_handler name)
        | Ok (EffHV (pat, cont_val, exph)) ->
          (match Result.map (fun t -> t) (run (lookup_in_env name state)) with
          | Error _ -> fail (No_effect name)
          | Ok _ ->
            let _ = match_pat pat (Eff2V (name, exval)) in
            eval_exp (extend_env cont_val (ContV cont_val) state) exph))
      | _ -> failwith "internal error")
    | EContinue (cont_val, exp) ->
      let _ =
        try lookup_in_env cont_val state with
        | Not_bound -> failwith "not a continuation value"
      in
      eval_exp state exp
    | EEffect1 name -> return (Eff1V name)
    | EEffect2 (name, exp) ->
      eval_exp state exp >>= fun evaled -> return (Eff2V (name, evaled))
  ;;

  let eval_dec state = function
    | DLet bindings ->
      (match bindings with
      | _, pat, exp ->
        let* evaled = eval_exp state exp in
        let* binds = match_pat pat evaled in
        let state =
          List.fold_left (fun state (id, v) -> extend_env id v state) state binds
        in
        return state)
    | DEffect1 (name, tyexp) ->
      let state = extend_env name (EffDec1V (name, tyexp)) state in
      return state
    | DEffect2 (name, tyexp1, tyexp2) ->
      let state = extend_env name (EffDec2V (name, tyexp1, tyexp2)) state in
      return state
  ;;
end

(* let test code expected =
  let module E = Interpret(Result) in 
  match Parser.parse Parser.decl code with
  | Result.Ok decl -> (match E.eval_dec (E.create_state()) decl with 
      | Result.Ok res -> true
      | _ -> res >>= fun res -> 
      )
  | _ -> print_string "Parse error"; false
)
;; *)

(* let test code expected =
   let open Interpret (Result) in
   match Parser.parse Parser.prog code with
   | Result.Ok prog -> Interpret prog expected
   | _ -> failwith "Parse error"
   ;;

   (* Eval test 1 *)

   (*
   let x = 1
 *)
   let%test _ = eval_test [ DLet (false, PVar "x", EConst (CInt 1)) ] "x -> 1; "

   (* Eval test 2 *)

   (*
   let (x, y) = (1, 2)
 *)
   (* let%test _ =
   eval_test
    [ DLet
        (false, PTuple [ PVar "x"; PVar "y" ], ETuple [ EConst (CInt 1); EConst (CInt 2) ])
    ]s
    "x -> 1 y -> 2 "
   ;; *)

   (* Eval test 3 *)

   (*
   let x = 3 < 2
 *)
   let%test _ =
   eval_test
    [ DLet (false, PVar "x", EOp (Less, EConst (CInt 3), EConst (CInt 2))) ]
    "x -> false; "
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
    "x -> 5; "
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
    "x -> 15; "
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
    "x -> 10; "
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
    "x -> 5; "
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
    "f -> x; "
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
    "a -> 3; f -> x; "
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
    "f -> x; kek -> y; lol -> 3; "
   ;;

   (* Eval test 12 *)

   (*
   let rec fact n =
   match n with
   | 0 -> 1
   | _ -> n * fact (n + -1)
   let x = fact 3
 *)
   let%test _ =
   eval_test
    [ DLet
        ( true
        , PVar "fact"
        , EFun
            ( PVar "n"
            , EMatch
                ( EVar "n"
                , [ PConst (CInt 0), EConst (CInt 1)
                  ; ( PWild
                    , EOp
                        ( Mul
                        , EVar "n"
                        , EApp
                            ( EVar "fact"
                            , EOp (Add, EVar "n", EUnOp (Minus, EConst (CInt 1))) ) ) )
                  ] ) ) )
    ; DLet (false, PVar "x", EApp (EVar "fact", EConst (CInt 3)))
    ]
    "fact -> n; x -> 6; "
   ;;

   (* Eval test 13 *)

   (*
   effect Failure: int -> int

   let helper x = 1 + perform (Failure x)

   let matcher x = match helper x with
     | effect (Failure s) k -> continue k (1 + s)
     | 3 -> 0 <- success if this one since both helper and effect perform did 1+
     | _ -> 100

   let y = matcher 1 <- must be 3 upon success
 *)
   let%test _ =
   eval_test
    [ DEffect2 ("Failure", TInt, TInt)
    ; DLet
        ( false
        , PVar "helper"
        , EFun
            ( PVar "x"
            , EOp (Add, EConst (CInt 1), EPerform (EEffect2 ("Failure", EVar "x"))) ) )
    ; DLet
        ( false
        , PVar "matcher"
        , EFun
            ( PVar "x"
            , EMatch
                ( EApp (EVar "helper", EVar "x")
                , [ ( PEffectH (PEffect2 ("Failure", PVar "s"), "k")
                    , EContinue ("k", EOp (Add, EConst (CInt 1), EVar "s")) )
                  ; PConst (CInt 3), EConst (CInt 0)
                  ; PWild, EConst (CInt 100)
                  ] ) ) )
    ; DLet (false, PVar "y", EApp (EVar "matcher", EConst (CInt 1)))
    ]
    "Failure -> Failure eff decl, 2 arg; helper -> x; matcher -> x; y -> 0; "
   ;;

   let%test _ =
   test
    {|
   effect E1: int

   let y = E1

   let helper x = 1 + perform (y)

   let res = match helper 1 with
   | effect (E1) k -> continue k (100)
   | 101 -> "correct"
   | _ -> "wrong"

   |}
    "E1 -> E1 eff dec, 1 arg; helper -> x; res -> correct; y -> E1 eff; "
   ;;

   let%test _ =
   test
    {|
   effect E: int -> int

   let helper x = match perform (E x) with
   | effect (E s) k -> continue k s*s
   | l -> l

   let res = match perform (E 5) with
   | effect (E s) k -> continue k s*s
   | l -> helper l
   |}
    "E -> E eff decl, 2 arg; helper -> x; res -> 625; "
   ;; *)
