open Ast

module EnvMap = struct
  include Map.Make (String)

  let pp pp_v ppf m =
    Format.fprintf ppf "@[[@[";
    iter (fun k v -> Format.fprintf ppf "@[\"%s\": %a@],@\n" k pp_v v) m;
    Format.fprintf ppf "@]]@]"
  ;;

  let pp_vars p = iter (fun k v -> p k v)
  let compare = compare
end

let empty_env_map = EnvMap.empty
let extend_env_map id x = EnvMap.add id x

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
  | FunV of pat * exp * state
  | Eff1V of capitalized_ident
  | Eff2V of capitalized_ident * exval
  | EffDec1V of capitalized_ident * tyexp
  | EffDec2V of capitalized_ident * tyexp * tyexp
  | ContV of ident
  | EffH of pat
[@@deriving show { with_path = false }]

and error =
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
  | Internal_Error
  | Catapulted of exval
[@@deriving show { with_path = false }]

and state =
  { env: exval EnvMap.t
  ; context: effhval EnvMap.t
  }
[@@deriving show { with_path = false }]

(* for pp to console *)
let pp_value k =
  let open Format in
  let () = fprintf std_formatter "val %s = " k in
  let rec helper fmt = function
    | IntV n -> fprintf fmt "%d" n
    | StringV s -> fprintf fmt "%S" s
    | BoolV b -> fprintf fmt "%b" b
    | TupleV l ->
      fprintf fmt "(%a)" (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt ", ") helper) l
    | ListV l ->
      fprintf fmt "[%a]" (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt "; ") helper) l
    | FunV (_, _, _) -> fprintf fmt "<fun>"
    | ContV _ -> fprintf fmt "continuation"
    | _ -> fprintf fmt "effect"
  in
  fun v ->
    let () = helper std_formatter v in
    print_newline ()
;;

let pp_env = EnvMap.pp_vars pp_value

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

  let create_state () = { env = EnvMap.empty; context = EnvMap.empty }

  let lookup_in_env id state =
    try return (lookup id state.env) with
    | Not_bound -> fail Not_bound
  ;;

  let lookup_in_context id state =
    try return (lookup id state.context) with
    | Not_bound -> fail Not_bound
  ;;

  let extend_env id v state = { state with env = extend_env_map id v state.env }

  let extend_context id v state =
    { state with context = extend_env_map id v state.context }
  ;;

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
    | PEffect1 name_p, Eff1V name_exp when name_p = name_exp -> return []
    | PEffect2 (name_p, p), Eff2V (name_exp, v) when name_p = name_exp -> match_pat p v
    | PEffectH (pat, _), Eff1V name_exp -> match_pat pat (Eff1V name_exp)
    | PEffectH (pat, _), Eff2V (name_exp, v) -> match_pat pat (Eff2V (name_exp, v))
    | PEffectH (pat1, _), EffH pat2 when pat1 = pat2 -> return []
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
    | ENil -> return (ListV [], false)
    | EConst x ->
      (match x with
      | CInt x -> return (IntV x, false)
      | CBool x -> return (BoolV x, false)
      | CString x -> return (StringV x, false))
    | EVar x ->
      (match run (lookup_in_env x state) with
      | Ok b -> return (b, false)
      | Error _ -> fail (Undef_var x))
    | EOp (op, x, y) ->
      let* exp_x, flag1 = eval_exp state x in
      (match exp_x with
      | EffH p -> return (EffH p, false)
      | a when flag1 -> return (a, true)
      | _ ->
        let* exp_y, flag2 = eval_exp state y in
        (match exp_y with
        | EffH p -> return (EffH p, false)
        | a when flag2 -> return (a, true)
        | _ ->
          (match run (apply_infix_op op exp_x exp_y) with
          | Ok x -> return (x, false)
          | Error x -> fail x)))
    | EUnOp (op, x) ->
      let* exp_x, flag1 = eval_exp state x in
      (match exp_x with
      | EffH p -> return (EffH p, false)
      | a when flag1 -> return (a, true)
      | _ ->
        (match run (apply_unary_op op exp_x) with
        | Ok x -> return (x, false)
        | Error x -> fail x))
    | ETuple exps ->
      (match exps with
      | hd :: tl ->
        let* hd_evaled, flag1 = eval_exp state hd in
        (match hd_evaled with
        | EffH p -> return (EffH p, false)
        | a when flag1 -> return (a, true)
        | _ ->
          let* tl_evaled, flag2 = eval_exp state (ETuple tl) in
          (match tl_evaled with
          | EffH p -> return (EffH p, false)
          | a when flag2 -> return (a, true)
          | TupleV exvals -> return (TupleV (hd_evaled :: exvals), false)
          | _ -> fail (Interp_error (ETuple exps))))
      | [] -> return (TupleV [], false))
    | ECons (exp1, exp2) ->
      let* exp1_evaled, flag1 = eval_exp state exp1 in
      (match exp1_evaled with
      | EffH p -> return (EffH p, false)
      | a when flag1 -> return (a, true)
      | _ ->
        let* exp2_evaled, flag2 = eval_exp state exp2 in
        (match exp2_evaled with
        | EffH p -> return (EffH p, false)
        | a when flag2 -> return (a, true)
        | ListV list -> return (ListV (exp1_evaled :: list), false)
        | x -> return (ListV [ exp1_evaled; x ], false)))
    | EIf (exp1, exp2, exp3) ->
      let* evaled, flag1 = eval_exp state exp1 in
      (match evaled with
      | EffH p -> return (EffH p, false)
      | a when flag1 -> return (a, true)
      | BoolV true -> eval_exp state exp2
      | BoolV false -> eval_exp state exp3
      | _ -> fail (Interp_error (EIf (exp1, exp2, exp3))))
    | ELet (bindings, exp1) ->
      let gen_state =
        fold bindings ~init:state ~f:(fun state binding ->
            let _, pat, exp = binding in
            let* evaled, flag1 = eval_exp state exp in
            match evaled with
            | EffH p -> fail (Catapulted (EffH p))
            | a when flag1 -> fail (Catapulted a)
            | _ ->
              let* binds = match_pat pat evaled in
              fold binds ~init:state ~f:(fun state (id, v) ->
                  return @@ extend_env id v state))
      in
      (match run gen_state with
      | Ok x -> eval_exp x exp1
      | Error x -> fail x)
    | EFun (pat, exp) -> return (FunV (pat, exp, state), false)
    | EApp (exp1, exp2) ->
      let* evaled, flag1 = eval_exp state exp1 in
      (match evaled with
      | EffH p -> return (EffH p, false)
      | a when flag1 -> return (a, true)
      | FunV (pat, exp, fstate) ->
        let* evaled2, flag2 = eval_exp state exp2 in
        (match evaled2 with
        | EffH p -> return (EffH p, false)
        | a when flag2 -> return (a, true)
        | _ ->
          let* binds = match_pat pat evaled2 in
          let new_state =
            List.fold_left (fun state (id, v) -> extend_env id v state) fstate binds
          in
          let very_new_state =
            match exp1 with
            | EVar x -> extend_env x evaled new_state
            | _ -> new_state
          in
          eval_exp { very_new_state with context = state.context } exp)
      | _ -> fail (Interp_error (EApp (exp1, exp2))))
    | EMatch (exp, mathchings) ->
      let effh = scan_cases mathchings in
      let exp_state =
        List.fold_left (fun state (id, v) -> extend_context id v state) state effh
      in
      let* evaled, _ = eval_exp exp_state exp in
      let rec do_match = function
        | [] -> fail (Match_exhaust (EMatch (exp, mathchings)))
        | (pat, exp) :: tl ->
          (match run (match_pat pat evaled) with
          | Ok binds ->
            let state =
              List.fold_left (fun state (id, v) -> extend_env id v state) state binds
            in
            eval_exp state exp
          | Error _ -> do_match tl)
      in
      do_match mathchings
    | EPerform exp ->
      let* eff, _ = eval_exp state exp in
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
            let* evaled, flag =
              eval_exp (extend_env cont_val (ContV cont_val) state) exph
            in
            if flag then return (evaled, false) else return (EffH pat, false)))
      | Eff2V (name, exval) ->
        let lookup = lookup_in_context name state in
        (match run lookup with
        | Error _ -> fail (No_handler name)
        | Ok (EffHV (pat, cont_val, exph)) ->
          (match run (lookup_in_env name state) with
          | Error _ -> fail (No_effect name)
          | Ok _ ->
            let* binds = match_pat pat (Eff2V (name, exval)) in
            let state =
              List.fold_left (fun state (id, v) -> extend_env id v state) state binds
            in
            let* evaled, flag =
              eval_exp (extend_env cont_val (ContV cont_val) state) exph
            in
            if flag then return (evaled, false) else return (EffH pat, false)))
      | _ -> fail Internal_Error)
    | EContinue (cont_val, exp) ->
      let _ =
        try lookup_in_env cont_val state with
        | Not_bound -> fail @@ Not_cont_val cont_val
      in
      (match run (eval_exp state exp) with
      | Ok (x, _) -> return (x, true)
      | Error x -> fail x)
    | EEffect1 name -> return (Eff1V name, false)
    | EEffect2 (name, exp) ->
      let* evaled, flag1 = eval_exp state exp in
      (match evaled with
      | EffH p -> return (EffH p, false)
      | a when flag1 -> return (a, true)
      | _ -> return (Eff2V (name, evaled), false))
  ;;

  let eval_dec state = function
    | DLet bindings ->
      (match bindings with
      | _, pat, exp ->
        let* evaled, _ = eval_exp state exp in
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

  let rec eval_prog state = function
    | hd :: tl ->
      (match Result.map (fun t -> t) (run (eval_dec state hd)) with
      | Ok x -> eval_prog x tl
      | Error x -> fail x)
    | [] -> return state
  ;;
end

open Interpret
open R

let test ~code =
  let open Format in
  match Parser.parse Parser.prog code with
  | Ok prog ->
    (match run (eval_prog (create_state ()) prog) with
    | Error x ->
      pp_error std_formatter x;
      false
    | Ok state ->
      pp_env state.env;
      (* pp_state std_formatter state;  *)
      true)
  | _ ->
    Printf.printf "Parse error";
    false
;;
