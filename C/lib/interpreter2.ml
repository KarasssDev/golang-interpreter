(* open Ast
open Parser


type v_value =
  | Vvoid
  | Vnull
  | Vint of int
  | Vfloat of float
  | Vdouble of float
  | Vchar of char
  | Vptr of v_value
  | Vstruct of (string, v_value) Hashtbl.t
  | Varray of (int * v_value) list
  | Vinitializer of expr list
  | Vmalloc of int
  | VheapAddr of string * int
  | VstackAddr of int
[@@deriving show {with_path= false}]
type struct_tags = (string, args list) Hashtbl.t [@@deriving show {with_path= false}]
type functions = (string, types * args list * statements) Hashtbl.t [@@deriving show {with_path= false}]
type vars = (string, (types * int * v_value)) Hashtbl.t [@@deriving show {with_path= false}]
type addr_vars = (int, string) Hashtbl.t [@@deriving show {with_path= false}]
type heap_t = (string, types * (int * v_value) list) Hashtbl.t [@@deriving show {with_path= false}]
type jump_stmt = None | Break | Next | Return of v_value [@@deriving show {with_path= false}]

type  exec_ctx =
    {
        local_vars: vars;
        local_vars_addr: addr_vars;
        struct_tags: struct_tags;
        jump_stmt: jump_stmt;
        last_value: v_value;
        dfunctions: functions;
        heap: heap_t;
        mutable index_local_vars: int;
    }
[@@deriving show {with_path= false}]

(* Interpreter.pp_exec_ctx Format.std_formatter a;; 
let start str = Interpreter.pp_exec_ctx Format.std_formatter @@ Result.get_ok @@ Interpreter.eval_main (Interpreter.make_exec_ctx ()) @@ Result.get_ok @@ Parser.parse Parser.prog str;;
*)

let rec printt = (function
    | Vvoid -> print_string "void"
    | Vnull -> print_string "null"
    | Vint i -> print_int i
    | Vfloat d
    | Vdouble d -> print_float d
    | Vchar c -> print_char c
    | Vptr pr ->
        print_string @@ "pointer base: "; (printt pr)
    | Vstruct _ -> print_string @@ "struct"
    | Varray hs -> (match hs with
        | (_, e)::_ -> printt e
        | _ -> print_string "")
    | Vmalloc ma -> print_string @@ "allocated bytes: " ^ (string_of_int ma)
    | VstackAddr sa -> print_string @@ "0x" ^ (string_of_int sa)
    | VheapAddr (na, addr) -> print_string @@ na ^ ", 0x" ^ (string_of_int addr)
    | Vinitializer _ -> print_string ""
)

module type MONAD = sig
  type 'a t

  val return : 'a -> 'a t
  val ( >>= ) : 'a t -> ('a -> 'b t) -> 'b t
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
end


let make_struct_mem_tb () = Hashtbl.create 5

let rec set_initial_value ctx typ =
    match typ with
    | CT_INT   -> Vint (0)
    | CT_CHAR   -> Vchar 'a'
    | CT_PTR _ -> Vptr Vnull
    | CT_VOID -> Vnull
    | CT_ARRAY _ -> Vvoid
    | CT_STRUCT tag ->
        let tr = make_struct_mem_tb () in
        let arg_ls = Hashtbl.find ctx.struct_tags tag in
        List.iter
            (fun (CARGS (t, n)) -> Hashtbl.add tr n (set_initial_value ctx t))
            arg_ls
        ; Vstruct tr

let make_exec_ctx () =
    {
        local_vars = Hashtbl.create 16;
        dfunctions = Hashtbl.create 16;
        local_vars_addr = Hashtbl.create 16;
        struct_tags = Hashtbl.create 16;
        last_value = Vvoid;
        jump_stmt = None;
        heap = Hashtbl.create 16;
        index_local_vars = 0;
    }

let copy_ctx ctx =
    {
        local_vars = Hashtbl.copy ctx.local_vars;
        local_vars_addr = Hashtbl.copy ctx.local_vars_addr;
        dfunctions = Hashtbl.copy ctx.dfunctions;
        struct_tags = Hashtbl.copy ctx.struct_tags;
        last_value = ctx.last_value;
        jump_stmt = ctx.jump_stmt;
        heap = Hashtbl.copy ctx.heap;
        index_local_vars = ctx.index_local_vars;
    }

(* let fmap_v_value f = (function
    | Vvoid -> Vvoid
    | Vnull -> Vnull
    | Vint i -> Vint (f i)
    | Vfloat ff -> Vfloat (f ff)
    | Vdouble f -> Vdouble (f ff)
    | Vchar c -> Vchar (f c)
    | Vptr bt -> Vptr (f bt)
    | Vstruct tb -> Vstruct (f tb)
    | Vinitializer c_exp_ls -> Vinitializer (List.map f c_exp_ls)
    | Vmalloc ma -> Vmalloc (f ma)
    | VheapAddr (pointed_name, addr) -> VheapAddr (pointed_name, f addr)
    | VstackAddr i -> VstackAddr (f i)
) *)

let fmap_varray f arr =
      match arr with
        | Varray ls -> Varray (f ls)
        | _ -> arr

let fmap_vstruct f v =
    match v with
    | Vstruct tb -> Vstruct (f tb)
    | _ -> v

let rec sizeof ctx = (function
    | CT_INT -> 4
    | CT_CHAR -> 1
    | CT_ARRAY (len, bt) -> len * (sizeof ctx bt)
    | CT_STRUCT tag ->
        List.fold_left (fun acc (CARGS (t, _)) -> sizeof ctx t + acc) 0 (Hashtbl.find ctx.struct_tags tag)
    | _ -> 8)

let get_ptr_typ tt =
    let rec get_p_t level ttt =
        match ttt with
        | CT_PTR t -> get_p_t (level + 1) t
        | _ -> (level, ttt)
    in
    get_p_t 0 tt

let add_value_struct stru mem_name v =
    match stru with
    | (Vstruct tr) -> Hashtbl.add tr mem_name v; Vstruct tr
    | _ -> stru

module Eval (M : MONADERROR) = struct
    open M

    let ht_replace ht k v = return @@ Hashtbl.replace ht k v

    let ht_find_opt_and_process ht key f emsg =
        match Hashtbl.find_opt ht key with Some v -> f v | None -> error emsg

    let ht_add ctx name typ v =
        let addr = ctx.index_local_vars in
        Hashtbl.add ctx.local_vars name (typ, addr, v);
        Hashtbl.add ctx.local_vars_addr addr name;
        ctx.index_local_vars <- addr + (sizeof ctx typ);
        return ctx

    let add_struct_tags ctx tag arg_list =
        Hashtbl.add ctx.struct_tags tag arg_list;
        return ctx

    let find_struct_components ctx tag =
        ht_find_opt_and_process ctx.struct_tags tag return
        
        let find_var ctx var_name =
        ht_find_opt_and_process ctx.local_vars var_name return

    let find_mem_value tb mem_name =
        ht_find_opt_and_process tb mem_name return

    let replace_mem_value tb mem_name vv =
        if Hashtbl.mem tb mem_name
            then (
            Hashtbl.replace tb mem_name vv;
            return tb
        ) else (
            error (mem_name ^ " does not exist")
        )

    let find_array_value arr ind =
        match arr with
        | Varray ls ->
            (match List.assoc_opt ind ls with
            | Some x -> return x
            | None -> error "Index in out of limits")
        | _ -> error "Unknown value for array operation"

    let replace_array_value arr ind len v =
        if ind < len && ind >= 0 then (
            return @@ fmap_varray (fun ls ->
            let new_array = List.remove_assoc ind ls
            in ((ind, v)::new_array)
            ) arr
        )
        else error "Index in out of limits"

    let find_var_typ ctx var_name =
        let (t, _, _ ) = Hashtbl.find ctx.local_vars var_name in t

    let find_heap_typ ctx var_name =
        let (t, _ ) = Hashtbl.find ctx.heap var_name in t

    let find_functions ctx func_name =
        ht_find_opt_and_process ctx.dfunctions func_name return

    let find_value_heap ctx name =
        ht_find_opt_and_process ctx.heap name return

    let def_stack_addr ctx addr =
        ht_find_opt_and_process ctx.local_vars_addr addr return
        "Invalid address"

    let find_value_heap_addr ctx addr =
        match addr with
            | Vptr (VheapAddr (pointed_name, addr)) ->
                find_value_heap ctx pointed_name "This memory operation is not allowed"
                >>= fun (_, blocks) ->
                    (match List.assoc_opt addr blocks with
                    | Some x -> return x
                    | _ -> error "Segmentation fault")
            | _ -> error "Invalid address type"

    let replace_in_heap ctx pointed_name addr v =
        find_value_heap ctx pointed_name "Invalid access to memory."
            >>= fun (typ, bs) ->
            if List.mem_assoc addr bs
            then (
                let new_st = List.remove_assoc addr bs in
                    Hashtbl.replace ctx.heap pointed_name (typ, (addr, v)::new_st);
                    return ctx
                )
            else error "Segmentation fault"

    let replace_in_heap_struct ctx pointed_name mem_name addr v =
        find_value_heap ctx pointed_name "Invalid access to memory."
            >>= fun (typ, bs) ->
            if List.mem_assoc addr bs
            then
                (
                    let new_stru =
                        fmap_vstruct
                            (fun tb -> Hashtbl.replace tb mem_name v; tb)
                            (List.assoc addr bs) in
                    let new_st = List.remove_assoc addr bs in
                        Hashtbl.replace ctx.heap pointed_name (typ, (addr, new_stru)::new_st);
                        return ctx;
                )
            else error "Segmentation fault"

    let full_malloc byt_n name ctx =
        find_var ctx name (name ^ " variable not found")
        >>= fun (tt, offset, _) ->
            let (_, base_typ) = get_ptr_typ tt in
            let gen_block nn size =
                let rec enum n size (s_acc, bs) =
                    if n = 0
                        then (s_acc, bs)
                        else enum (n - 1) size (s_acc + size, (s_acc, (set_initial_value ctx base_typ))::bs)
                in enum nn size (0, [])
            in
            let blocks = sizeof ctx base_typ in
            let num_blocks = byt_n / blocks in
            let (_, bs) = gen_block num_blocks blocks in
            (* Assign value *)
            Hashtbl.add ctx.heap name (base_typ, bs);

            (* Assign the address *)
            (* So far, one indirection pointer *)
            ht_replace ctx.local_vars name
                (tt, offset, Vptr (VheapAddr (name, 0)))
            >>= fun _ -> return ctx

            let get_name = function 
            | VAR_NAME name -> return name 
            | _ -> error "???"
    let free ctx name =
        find_var ctx name (name ^ " variable not found")
        >>= fun (typ, offs, ptr) ->
            (match ptr with
            | Vptr (VheapAddr (pointed_name, _)) ->
                Hashtbl.remove ctx.heap pointed_name;
                ht_replace ctx.local_vars name (typ, offs, Vptr (Vnull))
                >>= fun _ -> return ctx
            | _ -> error "It is valid for heap address")

    let _add v1 v2 =
        match (v1, v2) with
        | Vint o1, Vint o2 -> return @@ Vint (o1 + o2)
        | Vfloat o1, Vfloat o2 -> return @@ Vfloat (o1 +. o2)
        | Vdouble o1, Vdouble o2 -> return @@ Vdouble (o1 +. o2)
        | _ -> error "Unknown types"

    let _sub v1 v2 =
        match (v1, v2) with
        | Vint o1, Vint o2 -> return @@ Vint (o1 - o2)
        | Vfloat o1, Vfloat o2 -> return @@ Vfloat (o1 -. o2)
        | Vdouble o1, Vdouble o2 -> return @@ Vdouble (o1 -. o2)
        | _ -> error "Unknown types"

    let _mul v1 v2 =
        match (v1, v2) with
        | Vint o1, Vint o2 -> return @@ Vint (o1 * o2)
        | Vfloat o1, Vfloat o2 -> return @@ Vfloat (o1 *. o2)
        | Vdouble o1, Vdouble o2 -> return @@ Vdouble (o1 *. o2)
        | _ -> error "Unknown types"

    let _div v1 v2 =
        match (v1, v2) with
        | Vint o1, Vint o2 -> return @@ Vint (o1 / o2)
        | Vfloat o1, Vfloat o2 -> return @@ Vfloat (o1 /. o2)
        | Vdouble o1, Vdouble o2 -> return @@ Vdouble (o1 /. o2)
        | _ -> error "Unknown types"

    (*
        BOOLEAN AND RELATIONAL OPERATORS
    *)

    let bool_to_numf e = if e then 1.0 else 0.
    let bool_to_num e = if e then 1 else 0

    let _and v1 v2 =
        match (v1, v2) with
        | Vint o1, Vint o2 ->
            return @@ Vint (bool_to_num ((o1 > 0) && (o2 > 0)))
        | Vfloat o1, Vfloat o2 ->
            return @@ Vfloat (bool_to_numf ((o1 > 0.0) && (o2 > 0.0)))
        | Vdouble o1, Vdouble o2 ->
            return @@ Vdouble (bool_to_numf ((o1 > 0.0) && (o2 > 0.0)))
        | _ -> error "Unknown types"

    let _or v1 v2 =
        match (v1, v2) with
        | Vint o1, Vint o2 ->
            return @@ Vint (bool_to_num ((o1 > 0) || (o2 > 0)))
        | Vfloat o1, Vfloat o2 ->
            return @@ Vfloat (bool_to_numf ((o1 > 0.0) || (o2 > 0.0)))
        | Vdouble o1, Vdouble o2 ->
            return @@ Vdouble (bool_to_numf ((o1 > 0.0) || (o2 > 0.0)))
        | _ -> error "Unknown types"

    let _lt v1 v2 =
        match (v1, v2) with
        | Vint o1, Vint o2 ->
            return @@ Vint (bool_to_num (o1 < o2))
        | Vfloat o1, Vfloat o2 ->
            return @@ Vfloat (bool_to_numf (o1 < o2))
        | Vdouble o1, Vdouble o2 ->
            return @@ Vdouble (bool_to_numf (o1 < o2))
        | _ -> error "Unknown types"

     let _gt v1 v2 =
        match (v1, v2) with
        | Vint o1, Vint o2 ->
            return @@ Vint (bool_to_num (o1 > o2))
        | Vfloat o1, Vfloat o2 ->
            return @@ Vfloat (bool_to_numf (o1 > o2))
        | Vdouble o1, Vdouble o2 ->
            return @@ Vdouble (bool_to_numf (o1 > o2))
        | _ -> error "Unknown types"

    let _lte v1 v2 =
        match (v1, v2) with
        | Vint o1, Vint o2 ->
            return @@ Vint (bool_to_num (o1 <= o2))
        | Vfloat o1, Vfloat o2 ->
            return @@ Vfloat (bool_to_numf (o1 <= o2))
        | Vdouble o1, Vdouble o2 ->
            return @@ Vdouble (bool_to_numf (o1 <= o2))
        | _ -> error "Unknown types"


    let _gte v1 v2 =
        match (v1, v2) with
        | Vint o1, Vint o2 ->
            return @@ Vint (bool_to_num (o1 >= o2))
        | Vfloat o1, Vfloat o2 ->
            return @@ Vfloat (bool_to_numf (o1 >= o2))
        | Vdouble o1, Vdouble o2 ->
            return @@ Vdouble (bool_to_numf (o1 >= o2))
        | _ -> error "Unknown types"

    let _not v =
        match v with
        | Vint o1 -> return @@ Vint (if not (o1 > 0) then 1 else 0)
        | Vfloat o1 -> return @@ Vfloat (if not (o1 > 0.0) then 1. else 0.)
        | Vdouble o1 -> return @@ Vdouble (if not (o1 > 0.0) then 1. else 0.)
        | _ -> error "Unknown types"

    let _eq v1 v2 =
        match (v1, v2) with
        | Vint o1, Vint o2 ->
            return @@ Vint (bool_to_num (o1 == o2))
        | Vfloat o1, Vfloat o2 ->
            return @@ Vfloat (bool_to_numf (o1 == o2))
        | Vdouble o1, Vdouble o2 ->
            return @@ Vdouble (bool_to_numf (o1 == o2))
        | _ -> error "Unknown types"

    let _neq v1 v2 =
        match (v1, v2) with
        | Vint o1, Vint o2 ->
            return @@ Vint (bool_to_num (o1 == o2))
        | Vfloat o1, Vfloat o2 ->
            return @@ Vfloat (bool_to_numf (o1 == o2))
        | Vdouble o1, Vdouble o2 ->
            return @@ Vdouble (bool_to_numf (o1 == o2))
        | _ -> error "Unknown types"

    let eval_order_params ctx expr_list arg_list eval_f =
        let comp_args (e1, e2) =
            let comp x y =
                match (x, y) with
                    | ((CT_INT, _), (_, Vint _))
                    
                    | ((CT_CHAR, _), (_, Vchar _))
                      -> true
                    | ((CT_PTR typ1, _), (VAR_NAME name, _)) ->
                        CT_PTR typ1 = find_var_typ ctx name
                    | ((CT_PTR _, _), (_, Vptr _)) -> false
                    | _ -> false
            in comp e1 e2
        in
        let combined_args =
            List.combine
                (List.map (fun (CARGS (t, n)) -> (t, n)) arg_list)
                expr_list
        in
        let evaluated_args = List.map
            (fun (arg, expr) ->
                eval_f ctx expr >>= fun e -> return (e, arg, comp_args (arg, (expr, e))) )
            combined_args
        in return evaluated_args

    let check_type_params args =
        List.fold_left
            (fun ac e -> e
                >>= fun (_, _, b) -> ac
                >>= fun acc -> return (b && acc)
            )
            (return true) args

    let rec eval_expr ctx v =
        let op opp e1 e2 =
            eval_expr ctx e1 >>= fun t1 -> eval_expr ctx e2
                >>= fun t2 -> opp t1 t2
        in
        match v with
            | ADD (e1, e2)  -> op (_add) e1 e2
            | SUB (e1, e2)  -> op (_sub) e1 e2
            | MUL (e1, e2)  -> op (_mul) e1 e2
            | DIV (e1, e2)  -> op (_div) e1 e2

            (* BOOLEAN AND RELATIONAL OPERATORS *)
            | NOT e         -> eval_expr ctx e >>= fun ee -> _not ee
            | AND (e1, e2)  -> op _and e1 e2
            | OR (e1, e2)   -> op _or e1 e2
            | LT  (e1, e2)  -> op _lt e1 e2
            | LTE  (e1, e2) -> op _lte e1 e2
            | GT  (e1, e2)  -> op _gt e1 e2
            | GTE  (e1, e2)  -> op _gte e1 e2
            | EQUAL  (e1, e2)  -> op _eq e1 e2
            | NOT_EQUAL  (e1, e2)  -> op _neq e1 e2

            (* POINTER OPERATORS *)
            | DEREFERENCE df ->
                (match df with
                | VAR_NAME name ->
                    find_var ctx name (name ^ " variable not found")
                    >>= fun (_, _, addr) ->
                        find_value_heap_addr ctx addr
                | ACCESOR (name, mem_name) ->
                    get_name name >>= fun n -> find_var ctx n (n ^ " variable not found")
                    >>= fun (_, _, addr) ->
                    find_value_heap_addr ctx addr
                    >>= fun vtb ->
                        (match vtb with
                        | Vstruct tb ->
                            get_name mem_name >>= fun m_name -> find_mem_value tb m_name
                                ("This member" ^n ^ " does not exist")
                        | _ -> error "Invalid type for accessor")
                | _ -> error "Invalid operation")

            | ADDRESS expr ->
                (match expr with
                | VAR_NAME name ->
                    find_var ctx name (name ^ " variable not found")
                        >>= fun (_, addrp, _) -> return @@ Vptr (VstackAddr addrp)
                | _ -> error "Address operator is valid for variables")

            | INDEXER (var_name, expr) ->
                find_var ctx var_name (var_name ^ " variable not found")
                >>= fun (t, _, vv) ->
                    eval_expr ctx expr
                    >>= fun e ->
                        (match e with
                        | Vint ii when ii >= 0 ->
                            (match t with
                            | CT_PTR _ ->
                                let (_, base_t) = get_ptr_typ t in
                                (match vv with
                                | Vptr (VheapAddr (pointed_name, addr)) ->
                                    find_value_heap_addr ctx
                                        (Vptr (VheapAddr (pointed_name,
                                                    addr + (sizeof ctx base_t) * ii)
                                        ))

                                | _ -> error "Only pointer values must be used")
                            | CT_ARRAY (_,_) ->
                                find_array_value vv ii
                            | _ -> error "Indexer operator is available for pointers and arrays"
                            )
                        | _ -> error "Indexer works on positive integer values"
                        )

            (* | ACCESOR (var_name, mem_name) ->
                find_var ctx var_name (var_name ^ " variable not found")
                >>= fun (_, _, vv) ->
                    (match vv with
                    | Vstruct mem_tbl ->
                        find_mem_value mem_tbl mem_name (mem_name ^ " does not exist")
                    | _ -> error "Invalid operator for this type.") *)

            | LITERAL (CINT v)    -> return @@ Vint v
            | LITERAL (CCHAR c)  -> return @@ Vchar c
            | LITERAL (CVOID)  -> return Vvoid
            (* | LITERAL (CARRAY ls)  ->
                let rec convert_c_types = (function
                    | CINT i -> Vint i
                    | CCHAR c -> Vchar c
                    | CNULL -> Vnull
                    | CVOID -> Vvoid
                    | CARRAY arrs -> process arrs
                )
                and process arrs =
                    Varray (List.map (fun (i, e) -> (i, convert_c_types e)) arrs)
                in
                return @@ process ls *)

            | INITIALIZER ls -> return @@ Vinitializer ls

            | VAR_NAME name ->
                find_var ctx name (name ^ " local variable not found")
                >>= fun (_, _, vv) -> return vv

            (* | FUNC_CALL ("sizeof", expr_list) ->
                (match expr_list with
                | [VAR_NAME "int"] -> return @@ Vint (sizeof ctx CT_INT )
                | [VAR_NAME "char"] -> return @@ Vint (sizeof ctx CT_CHAR)
                | [VAR_NAME str_tag] ->
                    (match String.split_on_char ' ' str_tag with
                    | [stru_keyword; tag] ->
                        if String.equal stru_keyword "struct"
                            then return @@ Vint (sizeof ctx (CT_STRUCT tag))
                        else error "Unknown type for sizeof function"
                    | _ -> error "Unknown tag for a struct")
                | _ -> error "Unknown type for sizeof function.")

            | FUNC_CALL ("malloc", expr_list) ->
               (match expr_list with
                | [x] -> (eval_expr ctx x
                    >>= fun size ->
                        match size with
                        | Vint i -> return @@ Vmalloc i
                        | _ -> error "Wrong type")
                | _ -> error "Wrong number of parameters") *)

            | FUNC_CALL (name, expr_list) ->
                let comp_type e1 e2 =
                    match (e1, e2) with
                        | (CT_INT, Vint _)
                        | (CT_CHAR, Vchar _)
                        -> true
                        | (CT_PTR typ1, Vptr (VheapAddr (n, _))) ->
                            typ1 = find_heap_typ ctx n
                        | _ -> false
                in

                let ctx_func =
                    {ctx with
                        local_vars = Hashtbl.create 16;
                        local_vars_addr = Hashtbl.create 16;
                        jump_stmt = None;
                        last_value = Vvoid;
                    } in
                    let get_name = function 
                    | VAR_NAME name -> return name 
                    | _ -> error "???"
                  in
                  get_name name >>= fun n -> find_functions ctx n "function not found"
                    >>= fun (rettype, arg_list, blk) ->
                    let evaluated_args =
                        eval_order_params ctx expr_list arg_list eval_expr in
                    let checked = evaluated_args >>= check_type_params
                    in
                    checked >>= fun c ->
                        if c
                        then
                        (
                            evaluated_args >>=
                            List.fold_left (fun _ e ->
                                e >>= fun (v, (t, name), _) ->
                                ht_add ctx_func name t v
                                >>= fun _ -> return (t, v)
                            )
                            (return (CT_VOID, Vnull))
                            (* Execute el function body *)
                            >>= fun _ ->
                                eval_stmt ctx_func blk
                            >>= fun new_ctx ->
                                match new_ctx.jump_stmt with
                                | Return v ->
                                    if comp_type rettype v
                                    then return v
                                    else error ("In function call " ^ n ^
                                        ": mismatched types in return type.")
                                | _ -> error "unexpected break statement"

                            (* Eliminate variables inside this functions *)
                        )
                        else
                        (
                            error ("In function call " ^ n ^
                            ": mismatched types in formal args and passing args")
                        ) 
            | _ -> error "Unknown operator"

    and eval_stmt ctx = (function
        | VAR_DECL (name, typ, initial_value) ->
            (match initial_value with
                | Some v -> eval_expr ctx v
                    >>= (function
                    | Vmalloc size ->
                        ht_add ctx name typ (Vptr Vnull)
                        >>= fun new_ctx ->
                        full_malloc size name new_ctx

                    | Vinitializer expr_ls ->
                        (match typ with
                        | CT_STRUCT tag ->
                            find_struct_components ctx tag ("This " ^ tag ^ "is not found")
                            >>= fun comp_ls ->
                                let check_types x y =
                                    match (x, y) with
                                    | CT_INT,  LITERAL (CINT _)
                                    | CT_CHAR, LITERAL (CCHAR _)
                                    | CT_VOID, LITERAL (CVOID) -> true
                                    | _ -> false
                                in
                                let check_types =
                                    List.fold_left
                                        (fun ac (CARGS (t, _), e2) ->
                                            ac && check_types t e2)
                                        true
                                        (List.combine comp_ls expr_ls)
                                in
                                let mem_names_values =
                                    List.map
                                        (fun (CARGS (_, n), e) ->  (n, e))
                                        (List.combine
                                        comp_ls expr_ls)
                                in
                                if check_types
                                    then (
                                        let new_struct = Vstruct (Hashtbl.create 6) in
                                        let ready_struct = List.fold_left (
                                            fun ne (mem_name, e) ->
                                                ne >>= fun nee ->
                                                eval_expr ctx e >>=
                                                fun ee ->
                                                return @@ add_value_struct nee mem_name ee
                                        ) (return new_struct) mem_names_values
                                        in
                                        ready_struct >>= ht_add ctx name typ
                                    )
                                    else (
                                        error ("Arguments for initializing struct " ^ tag ^
                                                " have wrong types")
                                    )
                        | _ -> error "This type cannot be initialized as a list"
                        )
                    | vv -> ht_add ctx name typ vv
                    )
                | None ->
                    let init_v = try
                            return @@ set_initial_value ctx typ
                        with
                        | Not_found ->
                            (match typ with
                            | CT_STRUCT tag ->
                                error ("This tag " ^ tag ^ " is not found")
                            | _ -> error "Only use struct and a tag")
                    in
                    init_v >>= fun v -> ht_add ctx name typ v
                )

        | STRUCT_DECL (tag, args_list) -> add_struct_tags ctx tag args_list

        | T_ASSIGN (lvar, rexpr) ->
            (match lvar with
            | VAR_NAME name ->
                eval_expr ctx rexpr
                >>= fun outcome ->
                    (match outcome with
                    | Vmalloc size ->
                        full_malloc size name ctx
                    | _ ->
                        (
                            find_var ctx name (name ^ " not found")
                            >>= fun (t, offset, _) ->
                            ht_replace ctx.local_vars name (t, offset, outcome)
                            >>= fun _ -> return ctx
                        )
                    )

            | DEREFERENCE df ->
                (match df with
                | VAR_NAME name ->
                    find_var ctx name (name ^ " not found")
                    >>= fun (_, _, address) ->
                        (match address with
                        | Vptr (VheapAddr (pointed_name, addr)) ->
                            eval_expr ctx rexpr
                            >>= fun outc ->
                                replace_in_heap ctx pointed_name addr outc
                        | Vptr (VstackAddr addr) ->
                            eval_expr ctx rexpr
                            >>= fun outc ->
                            def_stack_addr ctx addr
                            >>= fun name ->
                            find_var ctx name (name ^ "not found")
                            >>= fun (t, addr, _) ->
                            ht_replace ctx.local_vars name (t, addr, outc)
                            >>= fun _ -> return ctx
                        | _ -> error "Invalid address")

                (* | ACCESOR (name, mem_name) ->
                    find_var ctx name (name ^ " not found")
                    >>= fun (_, _, address) ->
                        (match address with
                        | Vptr (VheapAddr (pointed_name, addr)) ->
                            eval_expr ctx rexpr
                            >>= fun outc ->
                                replace_in_heap_struct ctx pointed_name mem_name addr outc
                        | _ -> error "Invalid address") *)
                | _ -> error "Invalid identifier to deference")

            | INDEXER (var_name, expr) ->
                find_var ctx var_name (var_name ^ " not found")
                >>= fun (t, offset, address) ->
                    eval_expr ctx expr
                    >>= fun ind ->
                    (match ind with
                        | Vint ii ->
                            eval_expr ctx rexpr
                            >>= fun outcome ->
                            (match t with
                                | CT_PTR _ ->
                                    let (_, base_t) = get_ptr_typ t in
                                    (match address with
                                    | Vptr (VheapAddr (pointed_name, addr)) ->
                                        replace_in_heap ctx pointed_name
                                            (addr + (sizeof ctx base_t) * ii)
                                            outcome
                                    | _ -> error "Invalid address"
                                    )
                                | CT_ARRAY (len, _) ->
                                    replace_array_value address ii len outcome
                                    >>= fun vv ->
                                    ht_replace ctx.local_vars var_name (t, offset, vv)
                                    >>= fun _ -> return ctx

                                | _ -> error "Only pointer values must be used"
                            )
                        | _ -> error "Indexer operator is available for pointers and arrays"
                    )

            (* | ACCESOR (var_name, mem_name) ->
                find_var ctx var_name (var_name ^ " variable not found")
                >>= fun (_, _, vv) ->
                    (match vv with
                    | Vstruct mem_tbl ->
                        eval_expr ctx rexpr
                        >>= fun ee ->
                        replace_mem_value mem_tbl mem_name ee
                        >>= fun _ -> return ctx
                    | _ -> error "Invalid operator for this type.") *)

            | _ -> error "Assignment is for variables"
            )

        | RETURN e -> eval_expr ctx e
            >>= fun ee ->
                return {ctx with jump_stmt = Return ee; last_value = ee}

        | T_BLOCK stmt_list -> eval_block ctx stmt_list

        (* | PROC_CALL ("free", expr_list) ->
               (match expr_list with
                | [VAR_NAME var_name] ->
                    find_var ctx var_name (var_name ^ " variable not found")
                    >>= fun (_, _, vv) ->
                        (match vv with
                        | Vptr (VheapAddr (pointed_name, _)) ->
                            free ctx pointed_name
                        | Vptr (Vnull) -> return ctx
                        | _ -> error "Only pointer values must be used")
                | [_] -> error "Wrong type of parameter"
                | _ -> error "Wrong number of parameters")

        | PROC_CALL ("print", expr_list) ->
            List.iter (fun e ->
                ignore (eval_expr ctx e
                    >>= fun ee -> return @@ printt ee)
            ) expr_list;
            return ctx

        | PROC_CALL ("print_endline", expr_list) ->
            List.iter (fun e ->
                ignore (eval_expr ctx e
                    >>= fun ee -> return @@ printt ee)
            ) expr_list;
            print_endline "";
            return ctx

        | PROC_CALL (name, expr_list) ->
             let ctx_func =
                {ctx with
                    local_vars = Hashtbl.copy ctx.local_vars;
                    local_vars_addr = Hashtbl.copy ctx.local_vars_addr;
                    jump_stmt = None;
                    last_value = Vvoid
                }
            in
            find_functions ctx name "function not found"
                >>= fun (_, arg_list, blk) ->
                let evaluated_args =
                    eval_order_params ctx_func expr_list arg_list eval_expr in
                let checked = evaluated_args >>= check_type_params
                in
                checked >>= fun c ->
                    if c
                    then
                    (
                        evaluated_args >>=
                        List.fold_left (fun _ e ->
                            e >>= fun (v, (t, name), _) ->
                            ht_add ctx_func name t v
                            >>= fun _ -> return (t, v)
                            )
                        (return (CT_VOID, Vnull))
                        >>= fun _ ->
                            eval_stmt ctx_func blk
                            >>= fun _ ->
                                (* Making sure it does not return anything *)
                                return {ctx with
                                    jump_stmt = None;
                                    last_value = Vvoid
                                }
                    )
                    else
                    (
                        error ("In function call " ^ name ^
                        ": mismatched types in formal args and passing args")
                    ) *)
        | IF (guard, blk) ->
            eval_expr ctx guard
            >>= fun boo ->
                (match boo with
                | Vint b -> if b > 0 then eval_stmt ctx blk else return ctx
                | Vfloat b -> if b > 0.0 then eval_stmt ctx blk else return ctx
                | _ -> error "Use numbers for checking guards in if statements")

        | IF_ELSE (guard, blkif, blkelse) ->
            eval_expr ctx guard
            >>= fun boo ->
                (match boo with
                | Vint b ->
                    if b > 0
                    then eval_stmt ctx blkif
                    else eval_stmt ctx blkelse
                | Vfloat b ->
                    if b > 0.0
                    then eval_stmt ctx blkif
                    else eval_stmt ctx blkelse
                | _ -> error "Use numbers for checking guards in if statements")

        | WHILE (guard, blk) ->
            let rec whil () =
                eval_expr ctx guard >>=
                    fun cent ->
                        match cent with
                        | Vint i ->
                            if i > 0
                            then (eval_stmt ctx blk >>= fun _ -> whil ())
                            else return ctx
                        | Vfloat i ->
                            if i > 0.
                            then (eval_stmt ctx blk >>= fun _ -> whil ())
                            else return ctx
                        | _ -> error "Wrong Type at While statement"
            in whil ()

        | FOR (VAR_DECL (name, typ, initial_value), guard, step, blk) ->
            eval_stmt ctx (VAR_DECL (name, typ, initial_value))
                >>= fun new_ctx ->
                let rec exec_for ctx_for =
                    eval_expr ctx_for guard
                        >>= fun outcome ->
                        match outcome with
                        | Vint cent ->
                            if (cent > 0)
                            then (eval_stmt ctx_for blk
                                    >>= fun new_ctx_2 -> eval_stmt new_ctx_2 step
                                    >>= fun new_ctx_3 -> exec_for new_ctx_3)
                            else return ctx_for
                        | Vdouble cent
                        | Vfloat cent ->
                            if (cent > 0.)
                                then (eval_stmt ctx_for blk
                                    >>= fun new_ctx_2 -> eval_stmt new_ctx_2 step
                                    >>= fun new_ctx_3 -> exec_for new_ctx_3)
                            else return ctx_for
                        | _ -> error "Numeric data is only allowed"
                in exec_for new_ctx

        (* | POST_INCR (name, i)
        | PREF_INCR (name, i) ->
            find_var ctx name (name ^ " variable not found")
                >>= fun (t, offs, prev_v) ->
                    (match t with
                        | CT_PTR _ ->
                            let (_, base_t) = get_ptr_typ t in
                            (match prev_v with
                                | Vptr (VheapAddr (pointed_name, addr)) ->
                                    ht_replace ctx.local_vars name
                                    (t, offs, Vptr
                                        (
                                            VheapAddr
                                            (
                                                pointed_name,
                                                (addr + i * (sizeof ctx base_t))
                                            )
                                        )
                                    )
                                    >>= fun _ -> return ctx
                                | Vptr (VstackAddr addr) ->
                                    ht_replace ctx.local_vars name
                                    (t, offs, Vptr (VstackAddr (addr + i * (sizeof ctx base_t))))
                                    >>= fun _ -> return ctx
                                | _ -> error "Increment operator is not allowed for this pointer type"
                            )
                        | _ -> _add prev_v (Vint i)
                            >>= fun vv ->
                            ht_replace ctx.local_vars name (t, offs, vv)
                            >>= fun _ -> return ctx
                    )

        | PREF_DECR (name, i)
        | POST_DECR (name, i) ->
            find_var ctx name (name ^ " variable not found")
                >>= fun (t, offs, prev_v) ->
                    (match t with
                        | CT_PTR _ ->
                            let (_, base_t) = get_ptr_typ t in
                            (match prev_v with
                                | Vptr (VheapAddr (pointed_name, addr)) ->
                                    ht_replace ctx.local_vars name
                                    (t, offs, Vptr
                                        (
                                            VheapAddr
                                            (
                                                pointed_name,
                                                addr - i * (sizeof ctx base_t)
                                            )
                                        )
                                    )
                                    >>= fun _ -> return ctx
                                | Vptr (VstackAddr addr) ->
                                    ht_replace ctx.local_vars name
                                    (t, offs, Vptr (VstackAddr (addr - i * (sizeof ctx base_t))))
                                    >>= fun _ -> return ctx
                                | _ -> error "Increment operator is not allowed for this pointer type"
                            )
                        | _ -> _sub prev_v (Vint i)
                            >>= fun vv ->
                            ht_replace ctx.local_vars name (t, offs, vv)
                            >>= fun _ -> return ctx
                    ) *)

        | ASSIGN_SUB (lvar, rexpr) ->
            (match lvar with
            | VAR_NAME name -> eval_expr ctx rexpr
                >>= fun decr -> find_var ctx name (name ^ " variable not found")
                >>= fun (t, offs, prev_v) -> _sub prev_v decr >>= fun vv ->
                    ht_replace ctx.local_vars name (t, offs, vv);
                >>= fun _ -> return ctx

            | DEREFERENCE df ->
                (match df with
                | VAR_NAME name ->
                    find_var ctx name (name ^ " not found")
                    >>= fun (_, _, address) ->
                        (match address with
                        | Vptr (VheapAddr (pointed_name, addr)) ->
                            eval_expr ctx rexpr
                            >>= fun outc ->
                                replace_in_heap ctx pointed_name addr outc

                        | Vptr (VstackAddr addr) ->
                            eval_expr ctx rexpr
                            >>= fun decr ->
                            def_stack_addr ctx addr
                            >>= fun name ->
                            find_var ctx name (name ^ " not found")
                            >>= fun (t, addr, prev_v) ->
                            _sub prev_v decr
                            >>= fun vv ->
                            ht_replace ctx.local_vars name (t, addr, vv)
                            >>= fun _ -> return ctx
                        | _ -> error "Invalid address")
                | _ -> error "Invalid identifier to deference")
            | _ -> error "Assignment is for variables")

        | ASSIGN_ADD (lvar, rexpr) ->
            (match lvar with
            | VAR_NAME name -> eval_expr ctx rexpr
                >>= fun plus_expr -> find_var ctx name (name ^ " variable not found")
                >>= fun (t, offs, prev_v) -> _add prev_v plus_expr >>= fun vv ->
                    ht_replace ctx.local_vars name (t, offs, vv)
                >>= fun _ -> return ctx
            | DEREFERENCE df ->
                (match df with
                | VAR_NAME name ->
                    find_var ctx name (name ^ " not found")
                    >>= fun (_, _, address) ->
                        (match address with
                        | Vptr (VheapAddr (pointed_name, addr)) ->
                            eval_expr ctx rexpr
                            >>= fun outc ->
                                replace_in_heap ctx pointed_name addr outc

                        | Vptr (VstackAddr addr) ->
                            eval_expr ctx rexpr
                            >>= fun incr ->
                            def_stack_addr ctx addr
                            >>= fun name ->
                            find_var ctx name (name ^ " not found")
                            >>= fun (t, addr, prev_v) ->
                            _add prev_v incr
                            >>= fun vv ->
                            ht_replace ctx.local_vars name (t, addr, vv)
                            >>= fun _ -> return ctx
                        | _ -> error "Invalid address")
                | _ -> error "Invalid identifier to deference")
            | _ -> error "Assignment is for variables")

        | ASSIGN_MUL (lvar, rexpr) ->
            (match lvar with
            | VAR_NAME name -> eval_expr ctx rexpr
                >>= fun incr -> find_var ctx name (name ^ " variable not found")
                >>= fun (t, offs, prev_v) -> _mul prev_v incr >>= fun vv ->
                    ht_replace ctx.local_vars name (t, offs, vv)
                >>= fun _ -> return ctx
            | DEREFERENCE df ->
                (match df with
                | VAR_NAME name ->
                    find_var ctx name (name ^ " not found")
                    >>= fun (_, _, address) ->
                        (match address with
                        | Vptr (VheapAddr (pointed_name, addr)) ->
                            eval_expr ctx rexpr
                            >>= fun outc ->
                                replace_in_heap ctx pointed_name addr outc

                        | Vptr (VstackAddr addr) ->
                            eval_expr ctx rexpr
                            >>= fun incr ->
                            def_stack_addr ctx addr
                            >>= fun name ->
                            find_var ctx name (name ^ " not found")
                            >>= fun (t, addr, prev_v) ->
                            _mul prev_v incr
                            >>= fun vv ->
                            ht_replace ctx.local_vars name (t, addr, vv)
                            >>= fun _ -> return ctx
                        | _ -> error "Invalid address")
                | _ -> error "Invalid identifier to dereference")
            | _ -> error "Assignment is for variables")

        | ASSIGN_DIV (lvar, rexpr) ->
            (match lvar with
            | VAR_NAME name -> eval_expr ctx rexpr
                >>= fun decrr -> find_var ctx name (name ^ " variable not found")
                >>= fun (t, offs, prev_v) -> _div prev_v decrr >>= fun vv ->
                    ht_replace ctx.local_vars name (t, offs, vv)
                >>= fun _ -> return ctx
            | DEREFERENCE df ->
                (match df with
                | VAR_NAME name ->
                    find_var ctx name (name ^ " not found")
                    >>= fun (_, _, address) ->
                        (match address with
                        | Vptr (VheapAddr (pointed_name, addr)) ->
                            eval_expr ctx rexpr
                            >>= fun outc ->
                                replace_in_heap ctx pointed_name addr outc

                        | Vptr (VstackAddr addr) ->
                            eval_expr ctx rexpr
                            >>= fun decr ->
                            def_stack_addr ctx addr
                            >>= fun name ->
                            find_var ctx name (name ^ " not found")
                            >>= fun (t, addr, prev_v) ->
                            _div prev_v decr
                            >>= fun vv ->
                            ht_replace ctx.local_vars name (t, addr, vv)
                            >>= fun _ -> return ctx
                        | _ -> error "Invalid address")
                | _ -> error "Invalid identifier to deference")
            | _ -> error "Assignment is for variables")

        (* | FUNC_DECL (rettype, name, arg_ls, blk) ->
            let check_return ret bl =
                let comp_ret x y =
                    match (x, y) with
                    | CT_INT, CINT _
                    | CT_FLOAT, CFLOAT _
                    | CT_DOUBLE, CDOUBLE _
                    | CT_CHAR, CCHAR _
                    | CT_VOID, CVOID -> true
                    | _ -> false
                in
                let rec look_ret rr ls =
                    match ls with
                    | [] -> comp_ret ret CVOID
                    | [RETURN (LITERAL vv)] -> comp_ret rr vv
                    | _::lss -> look_ret rr lss
                in
                match bl with
                | T_BLOCK ls -> look_ret ret ls
                | _ -> false
            in
            if check_return rettype blk
                then
                (Hashtbl.add ctx.dfunctions name (rettype, arg_ls, blk);
                return ctx)
                else
                (error "Function type and return type must be equal") *)

        | _ -> error "Unknown statement")
    and eval_block ctxx stmts =
        (match stmts with
            | [] -> return ctxx
            | st::sts -> (
                eval_stmt ctxx st
                    >>= fun new_ctx ->
                    match new_ctx.jump_stmt with
                    | None -> eval_block new_ctx sts
                    | Return _ | Break | Next -> return new_ctx
                )
        )
    and eval_main_prog ctx = (function
        | C_PROG prog_ls ->
            List.iter (fun p -> ignore (eval_main_prog ctx p)) prog_ls;
            find_functions ctx "main" "main function not found"
            >>= fun (_, _, blk) -> eval_stmt ctx blk
       

        | C_PROG prog_ls ->
            List.iter (fun p -> ignore (eval_main_prog ctx p)) prog_ls;
            return ctx


        | C_INCLUDE _ -> return ctx
        | TOP_FUNC_DECL (rettype, name, arg_ls, blk) ->
            Hashtbl.add ctx.dfunctions name (rettype, arg_ls, blk);
            return ctx
        
        | TOP_STRUCT_DECL (tag, args_list) -> add_struct_tags ctx tag args_list
        
        | TOP_VAR_DECL (name, typ, initial_value) ->
            match initial_value with
                | Some v -> eval_expr ctx v
                    >>= fun vv -> ht_add ctx name typ vv
                    >>= fun _ -> return ctx
                | None -> ht_add ctx name typ (set_initial_value ctx typ)
                    >>= fun _ -> return ctx
    )
end


let eval ctx stmt =
    let module E = Eval (Result) in
    E.eval_stmt ctx stmt

let eval_main ctx prog =
    let module E = Eval (Result) in
    E.eval_main_prog ctx prog
(* 
let eval_inter ctx prog =
    let module E = Eval (Result) in
    match prog with
    | E_PROG pr -> E.eval_main_prog ctx pr
    | E_STATEMENTS stmts -> E.eval_stmt ctx stmts

let eval_test_ptr_struct ctx =
  Hashtbl.add ctx.struct_tags "tag" (
      [CARGS (CT_INT, "len");
        CARGS (CT_CHAR, "setX");
        CARGS (CT_DOUBLE, "setY");
        CARGS (CT_FLOAT, "setZ")]
  );
  let outc = eval ctx (T_BLOCK
        [
            VAR_DECL ("temp",  CT_PTR (CT_STRUCT "tag"),
            Some
             (FUNC_CALL ("malloc",
               [FUNC_CALL ("sizeof",
                 [VAR_NAME "struct tag"])])));
        ]
  )
  in outc *) *)
