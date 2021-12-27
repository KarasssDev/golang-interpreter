open Ast
open Bind
open Parser
open Std
open Format

module type FailFoldMonad = sig
  include Base.Monad.S2

  val fail : 'e -> ('a, 'e) t
  val fold : ('a, 'e) t -> ok:('a -> 'b) -> err:('e -> 'b) -> 'b
end

type value =
  | VInt of int
  | VString of string
  | VBool of bool
  | VExc of exc
  | VTuple of value list
  | VList of value list
  | VRef of value ref
  | VFun of string * ty * expr * env

(* refs are used for recursive functions *)
and env = value option ref BindMap.t [@@deriving eq]

let v_int n = VInt n
let v_string s = VString s
let v_bool b = VBool b
let v_exc exc = VExc exc
let v_tuple l = VTuple l
let v_list l = VList l
let v_ref v = VRef v
let v_fun prm prm_ty body env = VFun (prm, prm_ty, body, env)

let rec pp_value fmt = function
  | VInt n -> fprintf fmt "%d" n
  | VString s -> fprintf fmt "%S" s
  | VBool b -> fprintf fmt "%b" b
  | VExc exc -> pp_exc fmt exc
  | VTuple l ->
    fprintf fmt "(%a)" (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt ", ") pp_value) l
  | VList l ->
    fprintf fmt "[%a]" (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt "; ") pp_value) l
  | VRef v -> fprintf fmt "{contents = %a}" pp_value !v
  | VFun (_, _, _, _) -> fprintf fmt "<fun>"
;;

type run_err =
  | Unbound of string
  | Incorrect_ty of value
  | Exc of exc
  | Non_exhaustive of ptrn list
  | Div0
  | Invalid_rec of string
[@@deriving eq]

let pp_run_err fmt = function
  | Unbound s -> fprintf fmt "Unbound value %s" s
  | Incorrect_ty v -> fprintf fmt "Value %a has incorrect type" pp_value v
  | Exc e -> fprintf fmt "Exception: %a" pp_exc e
  | Non_exhaustive ps ->
    fprintf fmt "This pattern-matching is not exhaustive:\n%a" (pp_print_list pp_ptrn) ps
  | Div0 -> fprintf fmt "Division by zero"
  | Invalid_rec s ->
    fprintf
      fmt
      "This kind of expression is not allowed as right-hand side of `let rec %s`"
      s
;;

type run_ok_elm = string * (ty * value) [@@deriving eq]

let pp_run_ok_elm fmt (name, (ty, value)) =
  Format.fprintf fmt "val %s : %a = %a" name pp_ty ty pp_value value
;;

type run_ok = run_ok_elm list [@@deriving eq]

let pp_run_ok = pp_print_list pp_run_ok_elm

module Interpret (M : FailFoldMonad) : sig
  val run : program -> (run_ok, run_err) M.t
  val pp_res : formatter -> (run_ok, run_err) M.t -> unit
end = struct
  open M

  let lookup_val name env =
    match BindMap.find_opt name env with
    | None -> fail (Unbound name)
    | Some ref ->
      (match !ref with
      | None -> fail (Invalid_rec name)
      | Some v -> return v)
  ;;

  let add_val name value env = BindMap.add name (ref (Some value)) env

  (* `case_env` is `None` if `value` doesn't match `ptrn`,
     `case_env` is `Some(fail (Incorrect_ty value))` if `value` has incorrect type,
     `case_env` is `Some(return env)` if `value` matches `ptrn` *)
  let rec case_env value ptrn =
    match ptrn, value with
    | PVal s, _ -> Some (return (add_val s value BindMap.empty))
    | PConst (CInt c), VInt v when c = v -> Some (return BindMap.empty)
    | PConst (CInt _), VInt _ -> None
    | PConst (CString c), VString v when c = v -> Some (return BindMap.empty)
    | PConst (CString _), VString _ -> None
    | PConst (CBool c), VBool v when c = v -> Some (return BindMap.empty)
    | PConst (CBool _), VBool _ -> None
    | PConst CEmptyList, VList [] -> Some (return BindMap.empty)
    | PConst CEmptyList, VList _ -> None
    | PTuple ps, VTuple vs ->
      (match vs, ps with
      | [], [] -> Some (return BindMap.empty)
      | v :: vs, p :: ps ->
        mrg_case_envs (case_env v p) (fun () -> case_env (VTuple vs) (PTuple ps))
      | _ -> Some (fail (Incorrect_ty value)))
    | PCons (ps, pl), VList vs ->
      (match vs, ps with
      | (_ : value list), [] -> case_env value pl
      | v :: vs, p :: ps ->
        mrg_case_envs (case_env v p) (fun () -> case_env (VList vs) (PCons (ps, pl)))
      | _ -> None)
    | _ -> Some (fail (Incorrect_ty value))

  and mrg_case_envs env1 env2 =
    Option.bind env1 (fun env1 ->
        fold
          env1
          ~ok:(fun env1 ->
            Option.map
              (fun env2 ->
                env2 >>| fun env2 -> BindMap.add_seq (BindMap.to_seq env2) env1)
              (env2 ()))
          ~err:(fun err -> Some (fail err)))
  ;;

  let rec eval expr (env : env) =
    match expr with
    | EVal name -> lookup_val name env
    | EConst (CInt n) -> return (v_int n)
    | EConst (CString s) -> return (v_string s)
    | EConst (CBool b) -> return (v_bool b)
    | EConst CEmptyList -> return (v_list [])
    | EUnop (op, expr) ->
      eval expr env
      >>= fun value ->
      (match op, value with
      | Neg, VInt n -> return (v_int (-n))
      | Deref, VRef ref -> return !ref
      | _ -> fail (Incorrect_ty value))
    | EBinop (expr1, op, expr2) ->
      eval expr1 env
      >>= fun value1 ->
      (match value1, op with
      | VBool false, And -> return (v_bool false)
      | VBool true, Or -> return (v_bool true)
      | _ ->
        eval expr2 env
        >>= fun value2 ->
        (match value1, op, value2 with
        | VInt n, Add, VInt m -> return (v_int (n + m))
        | VInt n, Sub, VInt m -> return (v_int (n - m))
        | VInt n, Mul, VInt m -> return (v_int (n * m))
        | VInt _, Div, VInt m when m = 0 -> fail Div0
        | VInt n, Div, VInt m -> return (v_int (n / m))
        | VInt n, Eq, VInt m -> return (v_bool (n = m))
        | VInt n, Neq, VInt m -> return (v_bool (n != m))
        | VInt n, Les, VInt m -> return (v_bool (n < m))
        | VInt n, Leq, VInt m -> return (v_bool (n <= m))
        | VInt n, Gre, VInt m -> return (v_bool (n > m))
        | VInt n, Geq, VInt m -> return (v_bool (n >= m))
        | VString s1, Eq, VString s2 -> return (v_bool (s1 = s2))
        | VString s1, Neq, VString s2 -> return (v_bool (s1 != s2))
        | VBool b1, Eq, VBool b2 -> return (v_bool (b1 = b2))
        | VBool b1, Neq, VBool b2 -> return (v_bool (b1 != b2))
        | VBool _, And, VBool b2 | VBool _, Or, VBool b2 -> return (v_bool b2)
        | VRef ref, Asgmt, v ->
          ref := v;
          return (VTuple [])
        | v, Cons, VList l -> return (VList (v :: l))
        | _ -> fail (Incorrect_ty (VTuple [ value1; value2 ]))))
    | EApp (fn, arg) ->
      eval fn env
      >>= (function
      | VFun (prm, _, body, fn_env) ->
        eval arg env >>= fun arg -> eval body (add_val prm arg fn_env)
      | v -> fail (Incorrect_ty v))
    | ETuple l -> all (List.map (fun e -> eval e env) l) >>| v_tuple
    | ELet (decl, expr) -> add_decl decl env >>= eval expr
    | EMatch (scr, cases) ->
      eval scr env
      >>= fun value ->
      (match
         List.find_map
           (fun (ptrn, body) -> Option.map (fun env -> env, body) (case_env value ptrn))
           cases
       with
      | Some (case_env, body) ->
        case_env
        >>= fun case_env -> eval body (BindMap.add_seq (BindMap.to_seq case_env) env)
      | None -> fail (Non_exhaustive (List.map (fun (ptrn, _) -> ptrn) cases)))
    | EFun (prm, prm_ty, body) -> return (v_fun prm prm_ty body env)
    | ETry (scr, excs) ->
      fold
        (eval scr env)
        ~ok:(fun v -> return v)
        ~err:(function
          | Exc exc ->
            (match List.find_opt (fun (e, _) -> equal_exc exc e) excs with
            | None -> fail (Exc exc)
            | Some (_, expr) -> eval expr env)
          | err -> fail err)
    | ENative native ->
      lookup_val native_prm env
      >>= fun prm ->
      (match native, prm with
      | NPrintln, VString s ->
        printf "%s\n" s;
        return (VTuple [])
      | NRaise exc, VTuple [] -> fail (Exc exc)
      | NRef, _ -> return (VRef (ref prm))
      | NSneakyEff, VFun _ -> return prm
      | _ -> fail (Incorrect_ty prm))

  and add_decl decl env =
    if decl.is_rec
    then (
      let ref = ref None in
      let env = BindMap.add decl.name ref env in
      eval decl.expr env
      >>| fun v ->
      ref := Some v;
      env)
    else eval decl.expr env >>| fun v -> add_val decl.name v env
  ;;

  let stdlib_env =
    fold
      ~ok:(fun stdlib -> stdlib)
      ~err:(fun err ->
        eprintf "Error in stdlib: %a\n%!" pp_run_err err;
        exit 1)
      (List.fold_left
         (fun env decl -> env >>= fun env -> add_decl decl env)
         (return BindMap.empty)
         stdlib)
  ;;

  let run program =
    let _ = Tychk.check_program program in
    List.fold_left
      (fun acc decl ->
        acc
        >>= fun (env, vals) ->
        add_decl decl env
        >>= fun env ->
        lookup_val decl.name env
        >>| fun v -> env, (decl.name, (decl.ty, v)) :: List.remove_assoc decl.name vals)
      (return (stdlib_env, []))
      program
    >>| fun (_, res) -> List.rev res
  ;;

  let pp_res fmt res =
    fold res ~ok:(fun ok -> pp_run_ok fmt ok) ~err:(fun err -> pp_run_err fmt err)
  ;;
end

module InterpretResult = Interpret (struct
  include Base.Result

  let fold res ~ok ~err =
    match res with
    | Ok v -> ok v
    | Error v -> err v
  ;;
end)

let parse_and_run str =
  let ans =
    match parse str with
    | Ok program -> InterpretResult.run program
    | Error err ->
      eprintf "Parsing error:%s\n%!" err;
      exit 1
  in
  ans
;;

let pp_res = InterpretResult.pp_res
let pp_parse_and_run fmt str = pp_res fmt (parse_and_run str)
