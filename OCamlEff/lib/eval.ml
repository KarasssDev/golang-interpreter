open Ast
open Typing

module EnvMap = struct
  include Map.Make (String)

  let pp pp_v ppf m =
    Format.fprintf ppf "@[[@[";
    iter (fun k v -> Format.fprintf ppf "@[\"%s\": %a@],@\n" k pp_v v) m;
    Format.fprintf ppf "@]]@]"
  ;;
end

module type MONAD_FAIL = sig
  include Base.Monad.S2

  val run : ('a, 'e) t -> ok:('a -> ('b, 'e) t) -> err:('e -> ('b, 'e) t) -> ('b, 'e) t
  val fail : 'e -> ('a, 'e) t
  val ( let* ) : ('a, 'e) t -> ('a -> ('b, 'e) t) -> ('b, 'e) t
end

exception Not_bound

let lookup id env =
  try EnvMap.find id env with
  | Not_found -> raise Not_bound
;;

type effhval = EffHV of pat * ident * exp [@@deriving show { with_path = false }]

and exval =
  | IntV of int
  | BoolV of bool
  | StringV of string
  | TupleV of exval list
  | ListV of exval list
  | FunV of pat * exp * state Lazy.t
  | Eff1V of capitalized_ident
  | Eff2V of capitalized_ident * exval
  | EffDec1V of capitalized_ident * tyexp
  | EffDec2V of capitalized_ident * tyexp * tyexp
  | ContV of ident
  | EffH of pat
[@@deriving show { with_path = false }]

and error =
  | Match_fail of pat * exval (** Pattern matching failed *)
  | No_handler of capitalized_ident
      (** No effect handler found in context while doing perform *)
  | Not_bool_condition of exp (** Condition of an if-statement should be boolean *)
  | Not_effect_perform of exp (** Only effects can be performed *)
  | Not_function of exp (** Applying expression to not a function *)
  | No_effect of capitalized_ident (** No effect found in current state *)
  | Wrong_infix_op of infix_op * exval * exval
  | Wrong_unary_op of unary_op * exval
  | Undef_var of ident (** No such variable in current state *)
  | Match_exhaust of exp
  | Not_cont_val of ident (** Trying to continue not a continuation value *)
  | Not_bound of ident (** No such key in a map *)
  (* Needed to leave the whole expression in EMatch when perform did not have continue in its handler *)
  | Catapulted of exval (** Getting thrown out of expression evaluations *)
  (* Needed to leave the whole effect handler expression and return to the perform place when continue is fired *)
  | Catapulted_cont of exval
      (** Getting thrown out of expression evaluations when specifically continue is found *)
  | Let_rec_only_vars of pat (** let rec only allows PVar patterns *)
  | Division_by_zero
[@@deriving show { with_path = false }]

and state =
  { env: exval EnvMap.t
  ; context: effhval EnvMap.t
  }
[@@deriving show { with_path = false }]

(* for pp to console *)
let pp_value (k, t, v) =
  let open Format in
  let rec helper _ = function
    | IntV n -> printf "%d" n
    | StringV s -> printf "%S" s
    | BoolV b -> printf "%b" b
    | TupleV l -> printf "(%a)" (pp_print_list ~pp_sep:(fun _ _ -> printf ", ") helper) l
    | ListV l -> printf "[%a]" (pp_print_list ~pp_sep:(fun _ _ -> printf "; ") helper) l
    | FunV (_, _, _) -> printf "<fun>"
    | ContV _ -> printf "continuation"
    | _ -> printf "effect"
  in
  printf "val %s : %a = %a\n%!" k pp_ty t helper v
;;

module Interpret (M : MONAD_FAIL) = struct
  open M

  let fold list ~f ~init =
    let rec helper acc = function
      | [] -> acc
      | hd :: tl -> helper (acc >>= fun acc -> f acc hd) tl
    in
    helper (return init) list
  ;;

  let empty_state = { env = EnvMap.empty; context = EnvMap.empty }

  let lookup_env id state =
    try return (lookup id state.env) with
    | Not_bound -> fail @@ Not_bound id
  ;;

  let lookup_ctx id state =
    try return (lookup id state.context) with
    | Not_bound -> fail @@ Not_bound id
  ;;

  let extend_env id v state = { state with env = EnvMap.add id v state.env }
  let extend_ctx id v state = { state with context = EnvMap.add id v state.context }

  let extend_state state binds =
    List.fold_left (fun state (id, v) -> extend_env id v state) state binds
  ;;

  (* <-> means "matches" in examples *)
  let rec match_pat pat var =
    match pat, var with
    | PWild, _ -> return []
    | PVar name, v -> return [ name, v ]
    | PConst x, v ->
      (match x, v with
      | CInt a, IntV b when a = b -> return []
      | CString a, StringV b when a = b -> return []
      | CBool a, BoolV b when a = b -> return []
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
    | PEffect1 name_p, Eff1V name_exp when name_p = name_exp -> return [] (* E <-> E *)
    | PEffect2 (name_p, p), Eff2V (name_exp, v) when name_p = name_exp ->
      match_pat p v (* E x <-> E p *)
    | PEffectH (pat, _), Eff1V name_exp ->
      match_pat pat (Eff1V name_exp) (* | effect E cont <-> E *)
    | PEffectH (pat, _), Eff2V (name_exp, v) ->
      match_pat pat (Eff2V (name_exp, v)) (* | effect (E x) cont <-> E 5 *)
    | PEffectH (pat1, _), EffH pat2 when pat1 = pat2 ->
      return [] (* | effect E cont <-> E (direct pattern comparison) *)
    | a, b -> fail (Match_fail (a, b))
  ;;

  let apply_infix_op op x y =
    match op, x, y with
    | Add, IntV x, IntV y -> return (IntV (x + y))
    | Sub, IntV x, IntV y -> return (IntV (x - y))
    | Mul, IntV x, IntV y -> return (IntV (x * y))
    | Div, IntV _, IntV y when y = 0 -> fail Division_by_zero
    | Div, IntV x, IntV y -> return (IntV (x / y))
    (* "<" block *)
    | Less, IntV x, IntV y -> return (BoolV (x < y))
    | Less, StringV x, StringV y -> return (BoolV (x < y))
    | Less, TupleV x, TupleV y -> return (BoolV (x < y))
    | Less, ListV x, ListV y -> return (BoolV (x < y))
    (* "<=" block *)
    | Leq, IntV x, IntV y -> return (BoolV (x <= y))
    | Leq, StringV x, StringV y -> return (BoolV (x <= y))
    | Leq, TupleV x, TupleV y -> return (BoolV (x <= y))
    | Leq, ListV x, ListV y -> return (BoolV (x <= y))
    (* ">" block *)
    | Gre, IntV x, IntV y -> return (BoolV (x > y))
    | Gre, StringV x, StringV y -> return (BoolV (x > y))
    | Gre, TupleV x, TupleV y -> return (BoolV (x > y))
    | Gre, ListV x, ListV y -> return (BoolV (x > y))
    (* ">=" block *)
    | Geq, IntV x, IntV y -> return (BoolV (x >= y))
    | Geq, StringV x, StringV y -> return (BoolV (x >= y))
    | Geq, TupleV x, TupleV y -> return (BoolV (x >= y))
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
    | a, b, c -> fail (Wrong_infix_op (a, b, c))
  ;;

  let apply_unary_op op x =
    match op, x with
    | Minus, IntV x -> return (IntV (-x))
    | Not, BoolV x -> return (BoolV (not x))
    | a, b -> fail (Wrong_unary_op (a, b))
  ;;

  let scan_cases cases =
    List.filter_map
      (function
        | PEffectH (PEffect1 name, cont), exp ->
          Some (name, EffHV (PEffect1 name, cont, exp))
        | PEffectH (PEffect2 (name, pat), cont), exp ->
          Some (name, EffHV (PEffect2 (name, pat), cont, exp))
        | _ -> None)
      cases
  ;;

  let rec eval_exp state = function
    | ENil -> return (ListV [])
    | EConst x ->
      (match x with
      | CInt x -> return (IntV x)
      | CBool x -> return (BoolV x)
      | CString x -> return (StringV x))
    | EVar x -> run (lookup_env x state) ~ok:return ~err:fail
    | EOp (op, x, y) ->
      let* exp_x = eval_exp state x in
      let* exp_y = eval_exp state y in
      run (apply_infix_op op exp_x exp_y) ~ok:return ~err:fail
    | EUnOp (op, x) ->
      let* exp_x = eval_exp state x in
      run (apply_unary_op op exp_x) ~ok:return ~err:fail
    | ETuple exps ->
      M.all (List.map (eval_exp state) exps) >>= fun x -> return @@ TupleV x
    | ECons (exp1, exp2) ->
      let* exp1_evaled = eval_exp state exp1 in
      let* exp2_evaled = eval_exp state exp2 in
      (match exp2_evaled with
      | ListV list -> return (ListV (exp1_evaled :: list))
      | x -> return (ListV [ exp1_evaled; x ]))
    | EIf (exp1, exp2, exp3) ->
      run
        (eval_exp state exp1)
        ~ok:(function
          | BoolV true -> eval_exp state exp2
          | BoolV false -> eval_exp state exp3
          | _ -> fail (Not_bool_condition exp1))
        ~err:fail
    | ELet (bindings, exp1) ->
      let gen_state =
        fold bindings ~init:state ~f:(fun state binding ->
            let* _, st = eval_binding state binding in
            return st)
      in
      run gen_state ~ok:(fun s -> eval_exp s exp1) ~err:fail
    | EFun (pat, exp) -> return (FunV (pat, exp, lazy state))
    | EApp (exp1, exp2) ->
      let* evaled = eval_exp state exp1 in
      (match evaled with
      | FunV (pat, body, fstate) ->
        let* evaled2 = eval_exp state exp2 in
        let* binds = match_pat pat evaled2 in
        let new_state = extend_state { state with env = (Lazy.force fstate).env } binds in
        eval_exp new_state body
      | _ -> fail (Not_function exp1))
    | EMatch (exp, mathchings) ->
      let effh = scan_cases mathchings in
      let exp_state =
        List.fold_left (fun state (id, v) -> extend_ctx id v state) state effh
      in
      let* evaled = eval_exp exp_state exp in
      let rec do_match = function
        | [] -> fail (Match_exhaust (EMatch (exp, mathchings)))
        | (pat, exp) :: tl ->
          run
            (match_pat pat evaled)
            ~ok:(fun binds ->
              let state = extend_state state binds in
              eval_exp state exp)
            ~err:(fun _ -> do_match tl)
      in
      do_match mathchings
    | EPerform exp ->
      let* eff = eval_exp state exp in
      (match eff with
      | Eff1V name | Eff2V (name, _) ->
        let lookup = lookup_ctx name state in
        run
          lookup
          ~err:(fun _ -> fail (No_handler name))
          ~ok:(fun (EffHV (pat, cont_val, exph)) ->
            run
              (lookup_env name state)
              ~err:(fun _ -> fail (No_effect name))
              ~ok:(fun _ ->
                let* binds = match_pat pat eff in
                let state = extend_state state binds in
                run
                  (eval_exp (extend_env cont_val (ContV cont_val) state) exph)
                  ~ok:(fun _ -> return (EffH pat))
                  ~err:(function
                    | Catapulted_cont exval -> return exval
                    | a -> fail a)))
      | _ -> fail (Not_effect_perform exp))
    | EContinue (cont_val, exp) ->
      let _ =
        try lookup_env cont_val state with
        | Not_bound -> fail @@ Not_cont_val cont_val
      in
      run (eval_exp state exp) ~err:fail ~ok:(fun x -> fail (Catapulted_cont x))
    | EEffect1 name -> return (Eff1V name)
    | EEffect2 (name, exp) ->
      let* evaled = eval_exp state exp in
      return (Eff2V (name, evaled))

  and eval_binding state (is_rec, pat, exp) =
    if not is_rec
    then
      let* evaled = eval_exp state exp in
      let* binds = match_pat pat evaled in
      let extended = extend_state state binds in
      return (binds, extended)
    else
      let* id =
        match pat with
        | PVar id -> return id
        | other -> fail (Let_rec_only_vars other)
      in
      let* dummy =
        match exp with
        | EFun (pat, body) ->
          let rec new_env = lazy (extend_env id (FunV (pat, body, new_env)) state) in
          return @@ FunV (pat, body, new_env)
        | other -> eval_exp state other
      in
      let extended = extend_env id dummy state in
      let* evaled = eval_exp extended exp in
      return ([ id, evaled ], extend_env id evaled extended)
  ;;

  let eval_dec state = function
    | DLet binding -> eval_binding state binding
    | DEffect1 (name, tyexp) ->
      let ev = EffDec1V (name, tyexp) in
      let extended = extend_env name ev state in
      return ([ name, ev ], extended)
    | DEffect2 (name, tyexp1, tyexp2) ->
      let ev = EffDec2V (name, tyexp1, tyexp2) in
      let extended = extend_env name ev state in
      return ([ name, ev ], extended)
  ;;

  let eval_prog prog =
    let* binds, _ =
      fold
        ~f:(fun (binds, state) dec ->
          let* new_binds, new_state = eval_dec state dec in
          return (new_binds :: binds, new_state))
        ~init:([], empty_state)
        prog
    in
    return (binds |> List.rev |> List.flatten)
  ;;
end

module InterpreterResult = struct
  include Base.Result

  let run x ~ok ~err =
    match x with
    | Ok v -> ok v
    | Error e -> err e
  ;;

  let ( let* ) x f = x >>= f
end

let eval_pp _ code =
  let open Format in
  let open Interpret (InterpreterResult) in
  match Parser.parse Parser.prog code with
  | Ok prog ->
    (match infer_prog prog with
    | None -> ()
    | Some types ->
      InterpreterResult.run
        (eval_prog prog)
        ~err:(fun x -> printf "%a\n" pp_error x)
        ~ok:(fun binds ->
          List.iter pp_value (List.map2 (fun (k, v) (_, t) -> k, t, v) binds types)))
  | _ -> Printf.printf "Parse error"
;;
