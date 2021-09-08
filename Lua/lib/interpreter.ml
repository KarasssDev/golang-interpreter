open Ast
open Hashtbl_p

module type MONAD = sig
  type 'a t

  val return : 'a -> 'a t
  val ( >>= ) : 'a t -> ('a -> 'b t) -> 'b t
  val ( >> ) : 'a t -> 'b t -> 'b t
end

module type MONADERROR = sig
  include MONAD

  val error : string -> 'a t
end

module Result = struct
  type 'a t = ('a, string) Result.t

  let ( >>= ) = Result.bind
  let return = Result.ok
  let error = Result.error
  let ( >> ) x f = x >>= fun _ -> f
end

module Eval (M : MONADERROR) = struct
  open M

  let ( ++ ) lhs rhs =
    match (lhs, rhs) with
    | VNumber x, VNumber y -> return @@ VNumber (x +. y)
    | VNumber x, VString y -> return @@ VNumber (x +. float_of_string y)
    | VString x, VNumber y -> return @@ VNumber (float_of_string x +. y)
    | _ -> error "Unsupported operands type for (+)"

  let ( -- ) lhs rhs =
    match (lhs, rhs) with
    | VNumber x, VNumber y -> return @@ VNumber (x -. y)
    | VNumber x, VString y -> return @@ VNumber (x -. float_of_string y)
    | VString x, VNumber y -> return @@ VNumber (float_of_string x -. y)
    | _ -> error "Unsupported operands type for (-)"

  let ( ** ) lhs rhs =
    match (lhs, rhs) with
    | VNumber x, VNumber y -> return @@ VNumber (x *. y)
    | VNumber x, VString y -> return @@ VNumber (x *. float_of_string y)
    | VString x, VNumber y -> return @@ VNumber (float_of_string x *. y)
    | _ -> error "Unsupported operands type for (*)"

  let ( // ) lhs rhs =
    match (lhs, rhs) with
    | VNumber x, VNumber y -> return @@ VNumber (x /. y)
    | VNumber x, VString y -> return @@ VNumber (x /. float_of_string y)
    | VString x, VNumber y -> return @@ VNumber (float_of_string x /. y)
    | _ -> error "Unsupported operands type for (/)"

  (* Integer division *)
  let ( /// ) lhs rhs =
    match (lhs, rhs) with
    | VNumber x, VNumber y -> return @@ VNumber (Float.floor (x /. y))
    | VNumber x, VString y ->
        return @@ VNumber (Float.floor (x /. float_of_string y))
    | VString x, VNumber y ->
        return @@ VNumber (Float.floor (float_of_string x /. y))
    | _ -> error "Unsupported operands type for (//)"

  (* Remainder *)
  let ( %% ) lhs rhs =
    lhs /// rhs
    >>= function
    | VNumber int_part -> (
      match (lhs, rhs) with
      | VNumber x, VNumber y -> return @@ VNumber (x -. (int_part *. y))
      | VNumber x, VString y ->
          return @@ VNumber (x -. (int_part *. float_of_string y))
      | VString x, VNumber y ->
          return @@ VNumber (float_of_string x -. (int_part *. y))
      | _, _ -> error "Unsupported opearnds type for (%)" )
    | _ -> error "Unsupported opearnds type for (%)"

  let ( <<< ) lhs rhs =
    match (lhs, rhs) with
    | VNumber x, VNumber y -> return @@ VBool (x < y)
    | VNumber x, VString y -> return @@ VBool (x < float_of_string y)
    | VString x, VNumber y -> return @@ VBool (float_of_string x < y)
    | _ -> error "Uncomparable types"

  let ( <<<= ) lhs rhs =
    match (lhs, rhs) with
    | VNumber x, VNumber y -> return @@ VBool (x <= y)
    | VNumber x, VString y -> return @@ VBool (x <= float_of_string y)
    | VString x, VNumber y -> return @@ VBool (float_of_string x <= y)
    | _ -> error "Uncomparable types"

  let ( >>> ) lhs rhs =
    match (lhs, rhs) with
    | VNumber x, VNumber y -> return @@ VBool (x > y)
    | VNumber x, VString y -> return @@ VBool (x > float_of_string y)
    | VString x, VNumber y -> return @@ VBool (float_of_string x > y)
    | _ -> error "Uncomparable types"

  let ( >>>= ) lhs rhs =
    match (lhs, rhs) with
    | VNumber x, VNumber y -> return @@ VBool (x >= y)
    | VNumber x, VString y -> return @@ VBool (x >= float_of_string y)
    | VString x, VNumber y -> return @@ VBool (float_of_string x >= y)
    | _ -> error "Uncomparable types"

  let ( === ) lhs rhs =
    match (lhs, rhs) with
    | VNumber x, VNumber y -> return @@ VBool (x = y)
    | VNumber x, VString y -> return @@ VBool (x = float_of_string y)
    | VString x, VNumber y -> return @@ VBool (float_of_string x = y)
    | _ -> error "Uncomparable types"

  let ( !=== ) lhs rhs =
    match (lhs, rhs) with
    | VNumber x, VNumber y -> return @@ VBool (x <> y)
    | VNumber x, VString y -> return @@ VBool (x <> float_of_string y)
    | VString x, VNumber y -> return @@ VBool (float_of_string x <> y)
    | _ -> error "Uncomparable types"

  let is_true = function VBool false -> false | VNull -> false | _ -> true

  let string_of_value = function
    | VNumber v -> string_of_float v
    | VString v -> v
    | VBool v -> string_of_bool v
    | VTable _ -> "<table>"
    | VFunction _ -> "<function>"
    | VNull -> "nil"

  (* ==== Enviroment ==== *)

  type variables = (name, value) Hashtbl_p.t
  [@@deriving show {with_path= false}]

  type jump_statement = Default | Return | Break
  [@@deriving show {with_path= false}]

  type enviroment =
    { vars: variables
    ; last_value: value
    ; prev_env: enviroment option
    ; is_func: bool
    ; is_loop: bool
    ; jump_stmt: jump_statement
    ; last_env: enviroment option }
  (* last_env is needed in case we want to show variables scope after interpretation *)
  [@@deriving show {with_path= false}]

  let rec find_var varname = function
    | None -> return @@ VNull
    | Some env -> (
      match Hashtbl.find_opt env.vars varname with
      | Some v -> return @@ v
      | None -> find_var varname env.prev_env )

  let rec eval_expr env = function
    | Const v -> return v
    | ArOp (op, lhs, rhs) ->
        let get_op = function
          | Sum -> ( ++ )
          | Sub -> ( -- )
          | Mul -> ( ** )
          | Div -> ( /// )
          | FDiv -> ( // )
          | Mod -> ( %% ) in
        eval_expr env lhs
        >>= fun e_lhs ->
        eval_expr env rhs >>= fun e_rhs -> (get_op op) e_lhs e_rhs
    | RelOp (op, lhs, rhs) ->
        let get_op = function
          | Le -> ( <<< )
          | Leq -> ( <<<= )
          | Ge -> ( >>> )
          | Geq -> ( >>>= )
          | Eq -> ( === )
          | Neq -> ( !=== ) in
        eval_expr env lhs
        >>= fun e_lhs ->
        eval_expr env rhs >>= fun e_rhs -> (get_op op) e_lhs e_rhs
    | LogOp (op, lhs, rhs) ->
        let get_op = function And -> ( && ) | Or -> ( || ) in
        eval_expr env lhs
        >>= fun e_lhs ->
        eval_expr env rhs
        >>= fun e_rhs ->
        return @@ VBool ((get_op op) (is_true e_lhs) (is_true e_rhs))
    | UnOp (_, x) ->
        eval_expr env x >>= fun e_x -> return @@ VBool (not (is_true e_x))
    | Var v -> find_var v env
    | TableCreate el -> table_create env el
    | TableAccess (tname, texpr) -> table_find env tname texpr
    | CallFunc (n, el) -> (
        func_call env n el
        >>= fun e ->
        get_env e
        >>= fun env ->
        match env.jump_stmt with
        | Return -> return @@ env.last_value
        | _ -> return VNull )
    | _ -> error "Unexpected expression"

  and table_append ht env key = function
    | [] -> return @@ VTable ht
    | hd :: tl -> (
      match hd with
      | Assign (x, y) ->
          eval_expr env x
          >>= fun lhs ->
          eval_expr env y
          >>= fun rhs ->
          Hashtbl.replace ht (string_of_value lhs) rhs;
          table_append ht env key tl
      | _ ->
          eval_expr env hd
          >>= fun v ->
          Hashtbl.replace ht (string_of_int key) v;
          table_append ht env (key + 1) tl )

  and table_create env elist =
    let ht = Hashtbl.create 256 in
    table_append ht env 1 elist

  and table_find env tname texpr =
    let find_opt ht key =
      match Hashtbl.find_opt ht key with
      | Some v -> return @@ v
      | None -> return @@ VNull in
    find_var tname env
    >>= function
    | VTable ht -> (
        eval_expr env texpr
        >>= function
        | VNumber key -> find_opt ht (string_of_float key)
        | VString key -> find_opt ht key
        | _ -> error "Invalid key value" )
    | _ -> error "Attempt to index non-table value"

  and func_call env fname fargs =
    let create_vardec lnames lexprs =
      let rec helper l1 l2 acc =
        match (l1, l2) with
        | [], [] -> acc
        | hd1 :: tl1, hd2 :: tl2 -> (hd1, hd2) :: helper tl1 tl2 acc
        | hd1 :: tl1, [] -> (hd1, Const VNull) :: helper tl1 [] acc
        | [], _ :: _ -> acc in
      helper lnames lexprs [] in
    find_var fname env
    >>= function
    | VFunction (name_args, body) ->
        let var_args = List.map (fun x -> Var x) name_args in
        let block_with_vardec = function
          | Block b ->
              return
              @@ Block (Local (VarDec (create_vardec var_args fargs)) :: b)
          | _ -> error "Expected function body" in
        block_with_vardec body
        >>= fun b ->
        get_env env >>= fun en -> eval_stmt (Some {en with is_func= true}) b
    | _ -> error "Attempt to call not a function value"

  and eval_stmt env = function
    | Expression e ->
        eval_expr env e
        >>= fun v ->
        get_env env >>= fun en -> return @@ Some {en with last_value= v}
    | VarDec el ->
        eval_vardec true env el
        >>= fun env ->
        get_env env >>= fun en -> return @@ Some {en with last_value= VNull}
    | Local (VarDec el) ->
        eval_vardec false env el
        >>= fun env ->
        get_env env >>= fun en -> return @@ Some {en with last_value= VNull}
    | FuncDec (n, args, b) ->
        assign n (VFunction (args, b)) true env
        >>= fun _ ->
        get_env env >>= fun en -> return @@ Some {en with last_value= VNull}
    | Local (FuncDec (n, args, b)) ->
        assign n (VFunction (args, b)) false env
        >>= fun _ ->
        get_env env >>= fun en -> return @@ Some {en with last_value= VNull}
    | Local _ -> error "Invalid local statement"
    | If if_lst -> eval_if env if_lst
    | ForNumerical (fvar, finit, body) ->
        get_env env
        >>= fun env -> eval_for fvar finit body (Some {env with is_loop= true})
    | Block b -> create_next_env env >>= fun e -> eval_block (Some e) b
    | Return _ -> error "Unexpected return statement"
    | Break -> error "Unexpected break statement"
    | While (cond, body) ->
        get_env env
        >>= fun env -> eval_while cond body (Some {env with is_loop= true})

  and get_env = function
    | None -> error "Operation out of scope"
    | Some env -> return env

  and create_next_env = function
    | None ->
        return
        @@ { vars= Hashtbl.create 16
           ; last_value= VNull
           ; prev_env= None
           ; is_func= false
           ; is_loop= false
           ; jump_stmt= Default
           ; last_env= None }
    | Some env ->
        return @@ {env with prev_env= Some env; vars= Hashtbl.create 16}

  and eval_vardec is_global env = function
    | [] -> get_env env >>= fun en -> return @@ Some {en with last_value= VNull}
    | hd :: tl -> (
      match hd with
      | Var x, e ->
          eval_expr env e
          >>= fun v ->
          assign x v is_global env >>= fun en -> eval_vardec is_global en tl
      | TableAccess (tname, index), e -> (
          eval_expr env e
          >>= fun val_to_assign ->
          eval_expr env index
          >>= fun key ->
          find_var tname env
          >>= function
          | VTable t ->
              Hashtbl.replace t (string_of_value key) val_to_assign;
              eval_vardec is_global env tl
          | _ -> error "Attempt to index non-table value" )
      | _ -> error "Wrong type to assign to" )

  and assign n v is_global env =
    let rec set_global n v env =
      match env.prev_env with
      | None -> Hashtbl.replace env.vars n v
      | Some pe -> (
        match Hashtbl.find_opt env.vars n with
        | None -> set_global n v pe
        | Some _ -> Hashtbl.replace env.vars n v ) in
    match env with
    | None -> error "Operation out of scope"
    | Some e ->
        if is_global then (set_global n v e; return env)
        else (Hashtbl.replace e.vars n v; return env)

  and eval_if env = function
    | [] -> return env
    | hd :: tl -> (
      match hd with
      | cond, st ->
          eval_expr env cond
          >>= fun cond ->
          if is_true cond then eval_stmt env st else eval_if env tl )

  and eval_block env block =
    get_env env
    >>= fun env ->
    match block with
    | [] -> return @@ env.prev_env
    | [tl] -> (
      match tl with
      | Return v when env.is_func -> eval_return env v
      | Break when env.is_loop -> eval_break env
      | Break -> error "Error: Break statement is out of loop body"
      | Return _ -> error "Error: Return statement is out of function body"
      | _ -> (
          eval_stmt (Some env) tl
          >>= fun env ->
          get_env env
          >>= fun env ->
          match env.jump_stmt with
          | Return ->
              get_env env.prev_env
              >>= fun pr_env ->
              return
              @@ Some {pr_env with last_value= env.last_value; jump_stmt= Return}
          | Break -> eval_break env
          | _ -> (
            match env.prev_env with
            | None -> return @@ Some env
            | Some pr_env -> return @@ Some pr_env ) ) )
    | hd :: tl -> (
        eval_stmt (Some env) hd
        >>= fun env ->
        get_env env
        >>= fun env ->
        match env.jump_stmt with
        | Return ->
            get_env env.prev_env
            >>= fun pr_env ->
            return
            @@ Some {pr_env with last_value= env.last_value; jump_stmt= Return}
        | Break -> eval_break env
        | _ -> eval_block (Some env) tl )

  (* === This function sets last enviroment to show as a result of interpreter === *)
  and set_last_env env =
    match env.prev_env with
    | None -> print_string (show_enviroment env)
    | Some _ -> ()

  and eval_return env e =
    eval_expr (Some env) e
    >>= fun v ->
    get_env env.prev_env
    >>= fun pr_env ->
    return @@ Some {pr_env with last_value= v; jump_stmt= Return}

  and eval_break env =
    get_env env.prev_env
    >>= fun pr_env -> return @@ Some {pr_env with jump_stmt= Break}

  and eval_while cond body env =
    eval_expr env cond
    >>= fun predicate ->
    if is_true predicate then
      eval_stmt env body
      >>= fun env ->
      get_env env
      >>= fun env ->
      match env.jump_stmt with
      | Break -> return @@ Some {env with jump_stmt= Default}
      | Return -> return @@ Some {env with jump_stmt= Return}
      | _ -> eval_while cond body (Some env)
    else return env

  and eval_for fvar finit body env =
    let check_expr_number env num =
      eval_expr env num
      >>= function
      | VNumber v -> return v
      | _ -> error "bad 'for' initial value (number expected)" in
    let cond_to_floats = function
      | [start; stop; step] ->
          check_expr_number env start
          >>= fun start ->
          check_expr_number env stop
          >>= fun stop ->
          check_expr_number env step >>= fun step -> return [start; stop; step]
      | [start; stop] ->
          check_expr_number env start
          >>= fun start ->
          check_expr_number env stop >>= fun stop -> return [start; stop; 1.]
      | _ -> error "Bad 'for' constructor" in
    cond_to_floats finit >>= fun finit -> for_numerical fvar finit body env

  and for_numerical fvar finit body env =
    let create_local_vardec var value = Local (VarDec [(var, value)]) in
    let declare_init fvar start = function
      | Block b ->
          return
          @@ Block (create_local_vardec (Var fvar) (Const (VNumber start)) :: b)
      | _ -> error "Expected for body" in
    let rec helper start stop step body env =
      if start > stop then return env
      else
        declare_init fvar start body
        >>= fun body_with_init ->
        eval_stmt env body_with_init
        >>= fun env ->
        get_env env
        >>= fun env ->
        match env.jump_stmt with
        | Break -> return @@ Some {env with jump_stmt= Default}
        | Return -> return @@ Some {env with jump_stmt= Return}
        | _ -> helper (start +. step) stop step body (Some env) in
    match finit with
    | [start; stop; step] -> helper start stop step body env
    | _ -> error "Bad 'for' constructor"

  and eval_prog = function
    | None -> error "Syntax error occured"
    | Some p -> (
        eval_stmt None p
        >>= function
        | None -> error "Result enviroment is empty" | Some e -> return @@ e )
end

open Eval (Result)

(* Function to run interpreter *)

let eval parsed_prog =
  match eval_prog parsed_prog with
  | Ok res -> print_endline @@ show_enviroment res
  | Error m -> print_endline m
