open Ast
open Parser
open Base.Monad

(* open Base.Monad.Monad_intf *)
(* open Base.Monad_intf *)

(* type reg_value =
   Rval  v_value *)

type h_value = Vrval of string * v_value | Vdval of int * v_value

and v_value =
  (* | Vrval of string * v_value *)
  (* | Vdval of int * v_value *)
  | Vhval of h_value
  | Vint of int
  | Vchar of char
  | Vaddress of (types * int)
  | Vstaddress of (string * int)
  | Varraddress of (types * int)
  | Vstructval of string * v_value
  | Vvoid
  | Vnull (* | Vptr of v_value *)
  (* | Vstruct_vals of (string * types * v_value)  *)
  (* | Vstruct of (string, v_value) Hashtbl.t *)
  (* | Varray of (int * v_value) list *)
  | Vinitializer of expr list
  | Vmalloc of int * v_value
  (* | VheapAddr of string * int *)
  | Vvalues of v_value list
[@@deriving show { with_path = false }]

(* type g_vars = (string, types * int * h_value) Ast.Hashtbl.t
   [@@deriving show { with_path = false }] *)

type vars = (string, types * int * h_value) Ast.Hashtbl.t
[@@deriving show { with_path = false }]

type heap = (int, h_value) Ast.Hashtbl.t [@@deriving show { with_path = false }]

type functions = (string, types * args list * statements list) Ast.Hashtbl.t
[@@deriving show { with_path = false }]

type struct_tags = (string, (types * string) list) Ast.Hashtbl.t
[@@deriving show { with_path = false }]

type jump_stmt = None | Break | Next | Return of v_value
[@@deriving show { with_path = false }]

type allocated = (int * int) list [@@deriving show { with_path = false }]

(* type glob = {
     heap : heap;
     struct_tags : struct_tags;
     functions : functions;
     free_addr : int;
   } *)

type exec_ctx = {
  (* g_vars: g_vars; *)
  allocated : allocated;
  vars : vars;
  heap : heap;
  struct_tags : struct_tags;
  functions : functions;
  free_addr : int;
  pack_addr : int;
  jump_stmt : jump_stmt;
  last_value : v_value;
}
[@@deriving show { with_path = false }]

(* let g_vars' = Ast.Hashtbl.create 16
   let () = Hashtbl.add g_vars' "a" (CT_INT, 100, Vrval ("a", Vint 10) )> *)

let make_exec_ctx () =
  {
    (* g_vars = g_vars'; *)
    allocated = [];
    vars = Ast.Hashtbl.create 16;
    heap = Ast.Hashtbl.create 16;
    struct_tags = Ast.Hashtbl.create 16;
    functions = Ast.Hashtbl.create 16;
    jump_stmt = None;
    last_value = Vvoid;
    free_addr = 0;
    pack_addr = 0;
  }

let make_dep_ctx ctx () =
  {
    (* g_vars = ctx.g_vars; *)
    allocated = ctx.allocated;
    heap = ctx.heap;
    struct_tags = ctx.struct_tags;
    functions = ctx.functions;
    free_addr = ctx.free_addr;
    pack_addr = ctx.free_addr;
    vars = Ast.Hashtbl.create 16;
    jump_stmt = None;
    last_value = Vvoid;
  }

let dbg_print ctx palcs =
  (* print_string @@  *)
  "\n*******************\n" ^ "\nstruct_tags: "
  ^ show_struct_tags ctx.struct_tags
  ^ "\nfunctions: "
  ^ show_functions ctx.functions
  ^ "\nfree_addr: "
  ^ Int.to_string ctx.free_addr
  ^ "\nlast_value: "
  ^ show_v_value ctx.last_value
  ^ "\njump_stmt: "
  ^ show_jump_stmt ctx.jump_stmt
  ^ "\nallocated: " ^ show_allocated (List.sort compare palcs) ^ "\nheap: " ^ show_heap ctx.heap
  ^ "\nlocal_vars: " ^ show_vars ctx.vars

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

  let ( >> ) x f = x >>= fun _ -> f

  let return = Result.ok

  let extract = function
    | Error err -> Result.get_error err
    | Ok v -> Result.get_ok v

  let error = Result.error

  let get_ok = Result.get_ok
end

module Eval (M : MONADERROR) = struct
  open M

  let ht_find_opt_and_process ht key f emsg =
    match Ast.Hashtbl.find_opt ht key with Some v -> f v | None -> error emsg

  let smallest_type = CT_CHAR

  let take n l =
    let rec take' n l acc =
      match l with
      | h :: tl when n > 0 -> take' (n - 1) tl (h :: acc)
      | _ -> List.rev acc
    in
    take' n l []

  let rec take_after n l =
    match l with _ :: tl when n > 0 -> take_after (n - 1) tl | _ -> l

  let b_srch v l =
    let lft ps = take (List.length ps / 2) ps in
    let rgt ps = take_after (List.length ps / 2) ps in
    let rec b_srch' v = function
      | [ (l, r) ] -> l <= v && v <= r
      | ps when v < fst @@ List.hd @@ rgt ps -> b_srch' v @@ lft ps
      | ps -> b_srch' v @@ rgt ps
    in
    b_srch' v @@ List.sort compare l

  (* let sizeof = function
     | CT_INT | CT_PTR _ | CT_ARRAY _ | CT_STRUCT _ -> return 4
     | CT_CHAR ->
         return 1
         (* | CT_STRUCT ->  get_strct_types >>= fun ts -> foldl (+) 0 sizof .. ts*)
         (* | CT_ARRAY (size, tt) -> *)
         (* get_size tt >>= fun size_t -> return @@ (size * size_t) *)
     | CT_VOID -> error "Void haven't size" *)

  let get_size = function
    | CT_INT | CT_PTR _ | CT_ARRAY _ | CT_STRUCT _ -> return 4
    | CT_CHAR ->
        return 1
        (* | CT_STRUCT ->  get_strct_types >>= fun ts -> foldl (+) 0 sizof .. ts*)
        (* | CT_ARRAY (size, tt) -> *)
        (* get_size tt >>= fun size_t -> return @@ (size * size_t) *)
    | CT_VOID -> error "Void haven't size"
  (* | _ -> error "DBG: CT_STRUCT NEED" *)

  let get_cur_ctx = function
    | [] ->
        {
          (* g_vars = g_vars'; *)
          allocated = [];
          vars = Ast.Hashtbl.create 16;
          heap = Ast.Hashtbl.create 16;
          struct_tags = Ast.Hashtbl.create 16;
          functions = Ast.Hashtbl.create 16;
          jump_stmt = None;
          last_value = Vvoid;
          free_addr = 10007;
          pack_addr = 10007;
        }
    | c :: _ -> c

  let get_from_struct_tags ctxs tag =
    Ast.Hashtbl.find_opt (get_cur_ctx ctxs).struct_tags tag

  let rec sizeof (ctxs : exec_ctx list) t =
    match t with
    | CT_INT | CT_PTR _ | CT_CHAR _ | CT_VOID _ -> get_size t
    | CT_ARRAY (size, tt) -> sizeof ctxs tt >>= fun x -> return @@ (x * size)
    | CT_STRUCT tag -> (
        match get_from_struct_tags ctxs tag with
        | Some ps ->
            List.fold_left
              (fun acc (tt, _) ->
                acc >>= fun ac ->
                sizeof ctxs tt >>= fun inc -> return @@ (ac + inc))
              (return 0) ps
            >>= fun x ->
            get_size @@ CT_STRUCT "tag" >>= fun inc -> return @@ (x + inc)
        | None -> error "struct undeclared")

  (* get_size t *)

  let add_in_vars ctx name addr v t =
    match Hashtbl.find_opt ctx.vars name with
    | Some _ -> error @@ "name" ^ name ^ "already using"
    | None ->
        Ast.Hashtbl.add ctx.vars name (t, addr, v);
        return ctx

  (* let upd_free_addr ctxs addr =
       List.fold_left (fun acc ctx -> {ctx with free_addr = addr} :: acc) [] ctxs

     let upd_heap ctxs heap =
       List.fold_left (fun acc ctx -> {ctx with heap = heap} :: acc) [] ctxs
  *)

  let add_in_heap ctx addr v t =
    let rec set_nulls ctx i n =
      if i < n then (
        Hashtbl.add ctx.heap i (Vdval (i, Vnull));
        set_nulls ctx (i + 1) n)
      else ()
    in
    let cur_addr = ctx.free_addr in
    Ast.Hashtbl.add ctx.heap addr v;
    get_size t >>= fun size ->
    (* set_nulls ctx (cur_addr + 1) (cur_addr + size); *)
    return @@ { ctx with free_addr = cur_addr + size }

  let add_in_struct_tags ctx tag args =
    Ast.Hashtbl.add ctx.struct_tags tag args;
    return ctx

  let add_in_functions ctx name defs =
    Ast.Hashtbl.add ctx.functions name defs;
    return ctx

  let get_tail = function [] -> [] | _ :: t -> t

  let get_prev_env ctxs = get_cur_ctx @@ get_tail ctxs

  let get_prev_tl ctxs = get_tail @@ get_tail ctxs
  (* |t -> t *)

  let get_from_functions ctxs name =
    Ast.Hashtbl.find_opt (get_cur_ctx ctxs).functions name

  let get_from_heap ctxs addr =
    Ast.Hashtbl.find_opt (get_cur_ctx ctxs).heap addr

  let rec get_from_vars (ctxs : exec_ctx list) name in_fn =
    (* let a =  *)
    match ctxs with
    | [] -> error @@ "Var undefined []" ^ name
    | c :: cs when not in_fn ->
        if Option.is_none @@ Ast.Hashtbl.find_opt c.vars name then
          get_from_vars cs name in_fn
        else return @@ Ast.Hashtbl.find_opt c.vars name
    | _ -> return @@ Ast.Hashtbl.find_opt (get_cur_ctx ctxs).vars name

  (* in *)
  (* let b = return @@ Ast.Hashtbl.find_opt (get_cur_ctx ctxs).g_vars name in *)
  (* a >>= function | Some v -> return @@ Some v | None -> b *)

  let rec find_ctxs_with_var (ctxs : exec_ctx list) name =
    let rec helper (ctxs : exec_ctx list) name prevs =
      match ctxs with
      | [] -> error @@ "Var undefined ][" ^ name
      | c :: cs ->
          if Option.is_none @@ Ast.Hashtbl.find_opt c.vars name then
            helper cs name (c :: prevs)
          else return @@ (c :: cs, prevs)
      (* Ast.Hashtbl.find_opt c.vars name *)
    in
    helper ctxs name []

  let create_var ctxs name (v : v_value) t =
    match v with
    | Vhval (Vrval (_n, _v)) ->
        let ctx = get_cur_ctx ctxs in
        add_in_vars ctx name ctx.free_addr (Vrval (_n, _v)) t >>= fun ctx ->
        add_in_heap ctx ctx.free_addr (Vrval (_n, _v)) t
    | _ -> error "create_var"

  (* let rec conv_v0 = function
       | Vint _ -> CT_INT
       | Vchar _ -> CT_CHAR
       | Vaddress _ -> (CT_PTR CT_VOID )
       | Vmalloc (a, v') -> conv_v0 v'
            (* Vmalloc (a, ) *)
       | Vstructval (n, v') -> conv_v0 v'
       | _ -> _
           (* conv_v0 v v' >>= fun v'' -> return @@ Vstructval (n, v'') *)
       (* | Vvoid -> error "Void doesn't contain value" *)
       (* | _ -> error "2Unexpected expr" *)

     let create_nested_arr ctx = function
       | Vvalues vs -> List.fold_left (fun v -> _) ctx vs
           (* add_in_heap ctx ctx.free_addr (Vdval(ctx.free_addr, Vaddress 0)) (CT_ARRAY (0, CT_INT)) *)
       | _ -> _ *)

  let declare_struct ctx = function
    | TOP_STRUCT_DECL (name, args) ->
        let get_types (args : args list) =
          let get_pair (CARGS (t, n)) = (t, n) in
          List.fold_right (fun nt ts -> get_pair nt :: ts) args []
        in
        add_in_struct_tags ctx name (get_types args)
        (* >>= fun ctx -> return ctx *)
    | _ -> error "not a struct declaration"

  let declare_fun ctx = function
    | TOP_FUNC_DECL (ret_t, name, args, blk) -> (
        match blk with
        | T_BLOCK stmts ->
            add_in_functions ctx name (ret_t, args, stmts)
            (* >>= fun ctx -> return ctx *)
        | _ -> error "expected block")
    | _ -> error "not a struct function"

  let rec cast_default_arr_init (ctxs : exec_ctx list) size tt =
    let to_list = function Vvalues vs -> vs | otherwise -> [ otherwise ] in
    let rec helper (acc : v_value list) s t =
      if s > 0 then
        cast_default_init0 ctxs t >>= fun xs ->
        helper (acc @ to_list xs) (s - 1) t
        (* cast_default_init0 ctxs t >>= fun xs -> helper (acc @ [xs]) (s - 1) t *)
        (* >>= fun v -> _ *)
        (* >>= fun (ad, vs) -> helper (ad :: vs @ acc) (s - 1) t *)
      else return acc
    in
    (* helper [] size tt >>= fun x -> return @@ Vvalues x *)
    helper [] size tt

  and cast_default_struct_init (ctxs : exec_ctx list) tag =
    (* let rec tps =
         match get_from_struct_tags ctxs tag with
         | Some v ->
             (* List.fold_right
             (fun (t, n) acc ->
               acc >>= fun ac -> match t with
               | CT_ARRAY (size, tt) -> ( return [])
               | otherwise -> return @@ (otherwise, n) :: ac ) v (return [])  *)
             return v
         | None -> error "Struct undeclared"
       in *)
    let rec unpack_t (n : string) = function
      | CT_INT -> return [ (CT_INT, n) ]
      | CT_CHAR -> return [ (CT_CHAR, n) ]
      | CT_PTR t ->
          return [ (CT_PTR t, n) ]
          (* let fst (f, s) = f in *)
          (* unpack_t n t >>= fun t' -> return [(CT_PTR (fst (List.nth t' 0)) , n)] *)
      | CT_ARRAY (size, tt) ->
          let rec helper size tt acc =
            if size > 0 then
              unpack_t n tt >>= fun ntt' -> helper (size - 1) tt (acc @ ntt')
            else return acc
          in
          helper size tt [] >>= fun vs ->
          return @@ ((CT_ARRAY (size, tt), n) :: vs)
      | CT_STRUCT tag -> (
          match get_from_struct_tags ctxs tag with
          | Some tn ->
              let g =
                List.fold_right
                  (fun (t, n) acc ->
                    acc >>= fun ac ->
                    unpack_t n t >>= function
                    | [ t' ] -> return @@ (t' :: ac)
                    | t' :: ts' -> return @@ (t' :: ts') @ ac
                    | [] -> return ac)
                  tn (return [])
              in
              (* List.fold_right (fun acc (t, n) -> acc) (return []) vs *)
              g >>= fun x -> return @@ ((CT_STRUCT tag, n) :: x)
          | None -> error "Struct undeclared" (* error "" *))
      | CT_VOID -> return [ (CT_VOID, n) ]
    in

    (* let rec helper size tt acc = if size > 0 then tps tt >>= fun x -> helper (size - 1) tt (x :: acc) else acc in *)

    (* let rec struct_v cur_n = function | Vstructval (n, v) -> struct_v n v | otherwise -> (cur_n, otherwise) in *)
    (* tps  *)
    (* unpack_t tag @@ CT_STRUCT tag
       >>= fun tpss ->
       List.fold_right
         (fun (t, n) acc ->
           (* acc >>= fun vs ->         *)
           (*cast_default_init ctxs t >>= fun v -> return @@ (Vstructval (n, v) :: vs) *)
           acc >>= fun ac ->

           unpack_t n @@ t
           >>= fun x ->
           List.fold_right
           (fun (t', n') a -> a >>= fun a' -> cast_default_init ctxs t' >>= fun t'' ->
             return @@ Vstructval (n', t'') :: a' )
           x (return [])
           >>= fun xx -> return @@ xx @ ac
           (* return @@ x :: ac *)
           (* cast_default_init ctxs t >>= fun v -> return @@ (Vstructval (n, v) :: ac) *)
           (* List.fold_right (fun v acc' -> acc'
             >>= fun ac' ->
             (* let (n', v') = struct_v n v in *)
             (* return @@ (Vstructval (n', v)) :: ac')  *)
             return @@ (Vstructval (n, arg)) :: ac')
           vs (return ac) *)
         )
       tpss (return [])
       >>= fun x -> return @@ Vvalues x *)
    unpack_t tag @@ CT_STRUCT tag >>= function
    (* >>= fun tns ->  *)
    (* match tns with  *)
    | (_t, _) :: tl ->
        List.fold_right
          (fun (t, n) ac ->
            ac >>= fun a ->
            cast_default_init ctxs t >>= fun dv ->
            return @@ (Vstructval (n, dv) :: a))
          tl (return [])
        >>= fun vsts ->
        cast_default_init ctxs _t >>= fun x -> return @@ (x :: vsts)
        (* >>= h ->  *)
        (* return @@ vsts *)
    | _ -> error "DEF STRUCT"

  (* >>= function  *)
  (* | _ :: tl -> return tl *)
  (* | otherwise -> return otherwise *)

  (* and format_builder n = function
     | CT_STRUCT _ -> Vstructval (n, )
     | _ -> _ *)

  and cast_default_dep_v ctxs t n format =
    let ctx = get_cur_ctx ctxs in
    match format with
    | CT_STRUCT tag -> (
        match t with
        | CT_INT | CT_CHAR | CT_VOID | CT_PTR _ ->
            cast_default_init0 ctxs t >>= fun v ->
            add_in_heap ctx ctx.free_addr
              (Vdval (ctx.free_addr, Vstructval (n, v)))
              t
        | CT_STRUCT tag' ->
            get_size t >>= fun l ->
            add_in_heap ctx ctx.free_addr
              (Vdval
                 ( ctx.free_addr,
                   Vstructval (n, Vstaddress (tag', ctx.free_addr + l)) ))
              t
            (* add_in_heap ctx ctx.free_addr (Vdval (ctx.free_addr, Vstructval (n,(Vstaddress (ctx.free_addr + l))))) t *)
        | CT_ARRAY (_, t') ->
            get_size t >>= fun l ->
            add_in_heap ctx ctx.free_addr
              (Vdval
                 ( ctx.free_addr,
                   Vstructval (n, Varraddress (t', ctx.free_addr + l)) ))
              t)
    | _ -> (
        match t with
        | CT_INT | CT_CHAR | CT_VOID | CT_PTR _ ->
            cast_default_init0 ctxs t >>= fun v ->
            add_in_heap ctx ctx.free_addr (Vdval (ctx.free_addr, v)) t
        | CT_STRUCT tag ->
            get_size t >>= fun l ->
            add_in_heap ctx ctx.free_addr
              (Vdval (ctx.free_addr, Vstaddress (tag, ctx.free_addr + l)))
              t
        | CT_ARRAY (_, t') ->
            get_size t >>= fun l ->
            add_in_heap ctx ctx.free_addr
              (Vdval (ctx.free_addr, Varraddress (t', ctx.free_addr + l)))
              t)

  (* | CT_PTR _ ->  *)
  (* get_size t >>= fun l ->  *)
  (* add_in_heap ctx ctx.free_addr (Vdval (ctx.free_addr, Vstructval (n,(Varraddress (ctx.free_addr + l))))) t *)

  and cast_default_init0 ctxs = function
    | CT_INT -> return @@ Vint 0
    | CT_CHAR -> return @@ Vchar 'n'
    | CT_STRUCT n ->
        cast_default_struct_init ctxs n >>= fun x -> return @@ Vvalues x
    | CT_PTR tt -> return @@ Vaddress (tt, 0)
    | CT_ARRAY (size, tt) ->
        cast_default_arr_init ctxs size tt >>= fun x -> return @@ Vvalues x
    | CT_VOID -> error "void can't have values"

  and create_struct ctxs name vvs = function
    | CT_STRUCT tag -> (
        let ctx = get_cur_ctx ctxs in

        let tps =
          match get_from_struct_tags ctxs tag with
          | Some v ->
              (* List.fold_right (fun acc (t, n) -> acc) (return []) vs *)
              return v
          | None -> error "Struct undeclared"
        in
        let fst_val_addr =
          get_size @@ CT_STRUCT tag >>= fun s -> return @@ (ctx.free_addr + s)
        in
        (* tps >>= fun tpss -> ( *)
        match vvs with
        | Vvalues vs -> (
            (* (* let vss = [vs] in
               let _f ctx vs = *)
               return
               @@ List.map2 (fun tn v -> match tn with t, n -> (t, n, v)) tpss vs
               >>= fun tnvs ->
               List.fold_left
                 (fun  ctx (t, n, v)  ->
                   ctx >>= fun c ->
                   add_in_heap c c.free_addr
                     (Vdval (c.free_addr, v))
                     (* (Vstructval (n, v))  *) t)
                      (return ctx)  tnvs
               >>= fun ctx ->
               create_var (ctx :: get_tail ctxs) name
                 (Vhval (Vrval (name, Vaddress fst_val_addr)))
                 (CT_STRUCT tag) *)

            (* List.iter (fun v -> print_string @@ show_v_value v) vs;
               print_string "\n"; *)
            match vs with
            | _ :: tl ->
                fst_val_addr >>= fun ad ->
                create_var ctxs name
                  (Vhval (Vrval (name, Vstaddress (tag, ad))))
                  (CT_STRUCT tag)
                >>= fun ctx ->
                (* create_var ctxs name (Vhval (Vrval (name, Vstaddress ad))) (CT_STRUCT tag) >>= fun ctx -> *)
                let ctxs = ctx :: get_tail ctxs in
                List.fold_left
                  (fun c v ->
                    match v with
                    | Vstructval (n, v') ->
                        to_type v' >>= fun t ->
                        c >>= fun c ->
                        cast_default_dep_v c t n (CT_STRUCT tag) >>= fun x ->
                        return [ x ]
                    | _ -> error "XX")
                  (return ctxs) tl
                >>= fun x -> return @@ get_cur_ctx x
            | _ -> return @@ get_cur_ctx ctxs)
        | _ -> error @@ "expected set of values" ^ show_v_value vvs)
    | _ -> error "not a structure"

  and create_arr ctxs name (*(CT_ARRAY (size, tt))*) vvs (*(Vvalues vs)*) =
    function
    | CT_ARRAY (size, tt) -> (
        match vvs with
        | Vvalues vs ->
            let ctx = get_cur_ctx ctxs in
            let fst_val_addr =
              get_size @@ CT_ARRAY (size, tt) >>= fun s ->
              return @@ (ctx.free_addr + s)
            in
            fst_val_addr >>= fun ad ->
            create_var (ctx :: get_tail ctxs) name
              (Vhval (Vrval (name, Varraddress (tt, ad))))
              (CT_ARRAY (size, tt))
            >>= fun ctx ->
            let ctxs = ctx :: get_tail ctxs in

            List.fold_left
              (fun c v ->
                match v with
                | Vstructval (n, v') ->
                    to_type v' >>= fun t ->
                    c >>= fun c ->
                    cast_default_dep_v c t n (CT_STRUCT "tag") >>= fun x ->
                    return [ x ]
                | _ ->
                    to_type v >>= fun t ->
                    c >>= fun c ->
                    cast_default_dep_v c t "" (CT_ARRAY (0, CT_INT))
                    >>= fun x -> return [ x ])
              (* add_in_heap c c.free_addr (Vdval (c.free_addr, v)) tt)*)
              (return @@ ctxs)
              vs
            >>= fun x -> return @@ get_cur_ctx x
            (* >>= fun ctx ->
               create_var (ctx :: get_tail ctxs) name
                 (Vhval (Vrval (name, Vaddress fst_val_addr)))
                 (CT_ARRAY (size, tt)) *)
        | _ -> error @@ "expected set of values" ^ show_v_value vvs)
    | _ -> error "not an array"

  and to_type = function
    | Vint _ -> return CT_INT
    | Vchar _ -> return CT_CHAR
    | Vaddress (tt, _) -> return @@ CT_PTR tt
    | Vstructval (_, v) -> to_type v
    | Vstaddress (tag, _) -> return @@ CT_STRUCT tag
    | Varraddress _ -> return @@ CT_ARRAY (0, CT_INT)
    (* | Vvalues _ -> CT_PTR CT_VOID *)
    | _ -> error "to_type"

  and cast_default_init (ctxs : exec_ctx list) = function
    | CT_INT -> return @@ Vint 0
    | CT_CHAR -> return @@ Vchar 'n'
    (* | CT_STRUCT n -> cast_default_struct_init ctxs n *)
    | CT_STRUCT tag -> return @@ Vstaddress (tag, 0)
    | CT_PTR tt -> return @@ Vaddress (tt, 0)
    | CT_ARRAY (_, t) -> return @@ Varraddress (t, 0)
    (* | CT_ARRAY (size, tt) -> cast_default_arr_init ctxs size tt *)
    | CT_VOID -> error "void can't have values"

  let rec conv_to_addr tt = function
    (* | Vmalloc (_, v) -> conv_to_addr v *)
    | Vstructval (_, Vint v) | Vint v -> return @@ Vaddress (tt, v)
    | Vstructval (_, Vchar v) | Vchar v -> return @@ Vaddress (tt, Char.code v)
    | Vstructval (_, Vaddress v) | Vaddress v -> return @@ Vaddress v
    | Vnull -> return @@ Vaddress (tt, 0)
    | Varraddress (_, v) -> return @@ Vaddress (tt, v)
    (* | v -> return v *)
    | v -> error @@ "Adress expected" ^ show_v_value v

  let rec conv_to_int = function
    | Vint v -> return @@ Vint v
    | Vchar v -> return @@ Vint (Char.code v)
    | Vaddress (_, v) -> return @@ Vint v
    | Vnull -> return @@ Vint 0
    | Vstructval (_, v) -> conv_to_int v
    | a -> error @@ "Integer expected" ^ show_v_value a

  (* | _ -> error err_msg *)
  let rec conv_to_char = function
    | Vint v | Vaddress (_, v) ->
        return @@ Vchar (String.get (Int.to_string v) 0)
    | Vchar v -> return @@ Vchar v
    | Vnull -> return @@ Vchar 'n'
    | Vstructval (_, v) -> conv_to_char v
    | _ -> error "Char expected"

  let conv_t v = function
    | CT_INT -> conv_to_int v
    | CT_CHAR -> conv_to_char v
    | CT_PTR tt -> conv_to_addr tt v
    | CT_VOID -> error "Void doesn't contain value"
    | _ -> return v

  let rec conv_v v = function
    | Vint _ -> conv_t v CT_INT
    | Vchar _ -> conv_t v CT_CHAR
    | Vaddress (tt, _) -> conv_t v (CT_PTR tt)
    | Vmalloc (a, v') -> conv_v v v' >>= fun v'' -> return @@ Vmalloc (a, v'')
    | Vstructval (n, v') ->
        conv_v v v' >>= fun v'' -> return @@ Vstructval (n, v'')
    | Vvoid -> error "Void doesn't contain value"
    | _ -> error "2Unexpected expr"

  let rewrite_var ctxs name t v addr =
    let ctx_with_var = find_ctxs_with_var ctxs name in
    let p_d_ctx_tl =
      ctx_with_var >>= fun (ctxs, prevs) -> return @@ (get_cur_ctx ctxs, prevs)
    in
    let addr_fst =
      match get_from_heap ctxs addr with
      | Some (Vrval (_, Vaddress (_, ad))) -> return ad
      | Some (Vrval (_, Vstaddress (_, ad))) -> return ad
      | Some (Vrval (_, Varraddress (_, ad))) -> return ad
      | _ -> error "Var undefined rewrite_var"
    in
    let rec lift_vvs vs acc =
      match vs with
      | Vvalues vs' :: tl -> lift_vvs (vs' @ tl) (acc @ [ Vvalues [] ])
      | h :: tl -> lift_vvs tl (acc @ [ h ])
      | [] -> acc
    in
    p_d_ctx_tl >>= fun (d_ctx, prevs) ->
    match t with
    | CT_INT | CT_CHAR ->
        Hashtbl.replace d_ctx.vars name (t, addr, Vrval (name, v));
        Hashtbl.replace (get_cur_ctx ctxs).heap addr (Vrval (name, v));
        (* Hashtbl.replace d_ctx.heap addr (Vrval (name, v)); *)
        (* List.iter (fun x -> print_string (dbg_print x ^ "\n_______________________\n"))
           @@  prevs @ [ d_ctx ] @ get_tail ctxs; *)
        return @@ prevs @ [ d_ctx ] @ get_tail ctxs
    | CT_PTR tt ->
        conv_to_addr tt v >>= fun ad ->
        Hashtbl.replace d_ctx.vars name (t, addr, Vrval (name, ad));
        Hashtbl.replace (get_cur_ctx ctxs).heap addr (Vrval (name, ad));
        return @@ prevs @ [ d_ctx ] @ get_tail ctxs
    | CT_ARRAY (l, t) -> (
        match v with
        | Vvalues _vs ->
            (* List.iter (fun x -> print_string @@ show_v_value x) vs; *)
            (*
                         addr_fst >>= fun ad ->
                         (* checks for size...... приведение типов.....*)
                         get_size t >>= fun inc ->
                         List.fold_left
                           (fun  a v ->
                             a >>= fun a ->
                             (match get_from_heap ctxs a with
                               | Some (Vdval (_ad, vl)) -> return (_ad, vl)
                               | _ -> return (0, Vint 0)
                             )
                             >>= fun (_ad, ov) -> conv_v v ov
                             >>= fun v' ->
                             Hashtbl.replace d_ctx.heap _ad (Vdval (_ad, v'));
                             return @@ (a + inc))
                              (return ad) vs *)
            (* >>  *)
            addr_fst >>= fun ad ->
            cast_default_init0 ctxs @@ CT_ARRAY (l, t) >>= fun dv ->
            return @@ lift_vvs _vs [] >>= fun vs ->
            (match dv with
            | Vvalues dvs ->
                (* print_string "\n\n";
                   List.iter (fun x -> print_string @@ show_v_value x) vs;
                   print_string "\n\n";
                   List.iter (fun x -> print_string @@ show_v_value x) dvs;
                   print_string "\n\n--*-*-*-*-*---***-*-*-*-*-*-*-*-*-*-*-*-*-*-"; *)
                return
                @@ List.map2
                     (fun v d ->
                       match (v, d) with
                       | Vnull, _ -> d
                       | Vvalues _, Vstructval (_, Vstaddress _) -> d
                       (* | Vvalues _, Vstructval (_ , Vaddress _) -> d *)
                       | Vvalues _, Vstructval (_, Varraddress _) -> d
                       | otherwise, Vstructval (n, _) ->
                           Vstructval (n, otherwise)
                       | Vvalues _, Vstaddress _ -> d
                       | Vvalues _, Varraddress _ -> d
                       | _ -> v)
                     vs dvs
                >>= fun lifted_vs ->
                List.fold_right
                  (fun v acc ->
                    match v with
                    | Vstructval (_, v') ->
                        acc >>= fun ac ->
                        to_type v' >>= fun t ->
                        get_size t >>= fun inc -> return @@ (inc :: ac)
                    | otherwise ->
                        acc >>= fun ac ->
                        to_type otherwise >>= fun t ->
                        get_size t >>= fun inc -> return @@ (inc :: ac)
                    (* | _ -> acc *))
                  lifted_vs (return [])
                >>= fun incs ->
                (* print_string "\n\n";
                   List.iter (fun x ->  () ) incs;
                   print_string "\n\n"; *)
                (* return () *)
                (* print_string "\n\n";
                   List.iter (fun x -> print_string @@ Int.to_string x) incs;
                   print_string "\n\n";
                   List.iter (fun x -> print_string @@ show_v_value x) lifted_vs;
                   print_string "\n\n/*/*/*/*/*/*/*/*/*/*/*/*/*/*/*"; *)

                (* lifted_vs incs *)
                (* return () *)
                List.fold_left2
                  (fun a _v _inc ->
                    a >>= fun a ->
                    (match get_from_heap ctxs a with
                    | Some (Vdval (_ad, vl)) -> return (_ad, vl)
                    | _ -> error "!!!")
                    >>= fun (_ad, ov) ->
                    (* print_string "\n\n\n";
                       print_string @@ show_v_value ov;
                       print_string "\n";
                       print_string @@ show_v_value _v;
                       print_string "\n\n\n"; *)
                    match ov with
                    | Vstaddress _ | Varraddress _
                    | Vstructval (_, Vstaddress _)
                    | Vstructval (_, Varraddress _) ->
                        return @@ (a + _inc)
                    | _ ->
                        conv_v _v ov >>= fun v' ->
                        Hashtbl.replace d_ctx.heap _ad (Vdval (_ad, v'));
                        return @@ (a + _inc)
                    (* match get_from_heap ctxs a with
                         | Some (Vdval (_ad, vl)) -> return (_ad, vl)
                         | _ -> return (0, Vint 0)

                       >>= fun (_ad, ov) -> *)
                    (* >>= fun (_ad, ov) -> conv_v v ov
                       >>= fun v' ->
                       Hashtbl.replace d_ctx.heap _ad (Vdval (_ad, v'));
                       return (a + inc) *))
                  (return ad) lifted_vs incs
            | _ -> error "XYN")
            >> return @@ prevs @ [ d_ctx ] @ get_tail ctxs
        | Vaddress (_, a)
        | Varraddress (_, a)
        | Vstaddress (_, a)
        | Vstructval (_, Vaddress (_, a))
        | Vstructval (_, Varraddress (_, a))
        | Vstructval (_, Vstaddress (_, a)) ->
            Hashtbl.replace d_ctx.vars name
              (CT_ARRAY (l, t), addr, Vrval (name, Varraddress (t, a)));
            Hashtbl.replace (get_cur_ctx ctxs).heap addr
              (Vrval (name, Varraddress (t, a)));
            return @@ prevs @ [ d_ctx ] @ get_tail ctxs
        | a -> error @@ "Expected set of values" ^ " " ^ show_v_value a)
    | CT_STRUCT tag -> (
        addr_fst >>= fun ad ->
        match v with
        | Vvalues _vs ->
            cast_default_init0 ctxs @@ CT_STRUCT tag >>= fun dv ->
            return @@ lift_vvs _vs [] >>= fun vs ->
            (match dv with
            | Vvalues (_ :: dvs) ->
                return
                @@ List.map2
                     (fun v d ->
                       match (v, d) with
                       | Vvalues _, Vstructval (_, Vstaddress _) -> d
                       (* | Vvalues _, Vstructval (_ , Vaddress _) -> d *)
                       | Vvalues _, Vstructval (_, Varraddress _) -> d
                       | Vnull, _ -> d
                       | otherwise, Vstructval (n, _) ->
                           Vstructval (n, otherwise)
                       | _ -> d)
                     vs dvs
                >>= fun lifted_vs ->
                List.fold_right
                  (fun v acc ->
                    match v with
                    | Vstructval (_, v') ->
                        acc >>= fun ac ->
                        to_type v' >>= fun t -> return @@ (get_size t :: ac)
                    | _ -> acc)
                  lifted_vs (return [])
                >>= fun incs ->
                List.fold_left2
                  (fun a _v _inc ->
                    _inc >>= fun inc ->
                    a >>= fun a ->
                    (match get_from_heap ctxs a with
                    | Some (Vdval (_ad, Vstructval (nm, vl))) ->
                        return (_ad, nm, vl)
                    | _ -> return (0, "", Vint 0))
                    >>= fun (_ad, nm, ov) ->
                    match ov with
                    | Vstaddress _ | Varraddress _ -> return @@ (a + inc)
                    | _ ->
                        conv_v _v ov >>= fun v' ->
                        Hashtbl.replace d_ctx.heap a
                          (Vdval (_ad, Vstructval (nm, v')));
                        return @@ (a + inc))
                  (return ad) lifted_vs incs
            | _ -> error "CT_STRUCT__")
            >> return @@ prevs @ [ d_ctx ] @ get_tail ctxs
        | Vaddress (_, a)
        | Varraddress (_, a)
        | Vstaddress (_, a)
        | Vstructval (_, Vaddress (_, a))
        | Vstructval (_, Varraddress (_, a))
        | Vstructval (_, Vstaddress (_, a)) ->
            Hashtbl.replace d_ctx.vars name
              (t, addr, Vrval (name, Vstaddress (tag, a)));
            Hashtbl.replace (get_cur_ctx ctxs).heap addr
              (Vrval (name, Vstaddress (tag, a)));
            return @@ prevs @ [ d_ctx ] @ get_tail ctxs
        | _ -> error "Expected set of values")
    | _ -> error "1"

  (* val stmt_eval : exec_ctx -> statements -> exec_ctx *)

  let rec eval_stmt (ctxs : exec_ctx list) (in_fn : bool) (convt : types)
      (palcs : allocated) = function
    | VAR_DECL (name, t, expr) ->
        declare ctxs name t expr in_fn convt palcs
        (* >>= fun c -> match expr with  *)
        (* | Some e ->  *)
        (* eval_stmt c @@ EXPRESSION e  *)
        >>=
        fun (ctx', pls) ->
        (* print_string "\n\n";
           print_string "here";
           print_string "\n";
           print_string @@ dbg_print @@ get_cur_ctx ctx';
           print_string "\n\n"; *)
        return (ctx', pls)
        (* | None -> return c *)
    | T_BLOCK stmts ->
        eval_block_fn ctxs in_fn convt palcs stmts >>= fun x ->
        (* print_string @@ "\n\n BBB: ";
           List.iter (fun x -> print_string @@ dbg_print @@ x) x;
           print_string "\n\n"; *)
        return x
    | T_ASSIGN (l, r) ->
        (* print_string "\n###############";
           List.iter (fun x -> print_string @@ dbg_print x)  ctxs;
           print_string "\n###############";
           print_string "\n";
           print_string "\n"; *)
        assign ctxs l r in_fn convt palcs
    | EXPRESSION (FUNC_CALL (n, vs)) ->
        eval_expr ctxs in_fn convt palcs @@ FUNC_CALL (n, vs)
        >>= fun ((ctxs', lv), pls) -> return (ctxs', pls)
    | RETURN e ->
        eval_expr ctxs in_fn convt palcs e >>= fun ((ctxs', v), pls) ->
        (* print_string @@ "\n\n EHRE: ";
           print_string @@ dbg_print @@ get_cur_ctx ctxs';
           print_string "\n\n"; *)
        return
        @@ {
             (get_cur_ctx ctxs) with
             jump_stmt = Return v;
             last_value = get_val v;
             free_addr = (get_cur_ctx ctxs').free_addr;
           }
           :: get_tail ctxs
        (*
           >>= fun cs' -> return @@ upd_free_addr cs' (get_cur_ctx cs').free_addr
           >>= fun cs' -> return @@ upd_heap cs' (get_cur_ctx cs').heap *)
        >>=
        fun cs'' ->
        (* print_string @@ "\n\n RRR: ";
           List.iter (fun x -> print_string @@ dbg_print @@ x) cs'';
           print_string "\n\n"; *)
        return (cs'', pls)
    (*return @@ { (get_cur_ctx ctxs) with jump_stmt = Return v; last_value = v } *)
    (* | TOP_FUNC_DECL (t, name, args, stmts) *)
    | _ -> return (ctxs, palcs)

  (* error "eval_stmt" *)
  and mk_prefix = function Some (FUNC_CALL _) -> "." | _ -> "."

  and declare (ctxs : exec_ctx list) name t (expr : expr option) in_fn convt
      palcs =
    (* let ctx = get_cur_ctx ctxs in *)
    (* match expr with *)
    let prfx = mk_prefix expr in

    (match t with
    | CT_INT | CT_CHAR 
    (* | CT_PTR _  *)
      -> (
        cast_default_init ctxs t >>= fun v ->
        create_var ctxs (prfx ^ name) (Vhval (Vrval (prfx ^ name, v))) t
        >>= fun h ->
        (* create_var ctxs (name) (Vhval (Vrval (name, v))) t >>= fun h -> *)
        match expr with
        | None ->
            return @@ (h :: get_tail ctxs, palcs)
            (* >>= fun s_ctx ->
               let nahv = get_from_vars s_ctx (prfx^name) in_fn >>= function | Some v -> return v | None -> error "" in
               nahv >>= fun (t, a, hv) ->
               Hashtbl.add (get_cur_ctx ctxs).vars name (t, a, Vrval (name, get_val @@ Vhval hv));
               Hashtbl.replace (get_cur_ctx ctxs).heap a (Vrval (name, get_val @@ Vhval hv));
               Hashtbl.remove (get_cur_ctx ctxs).vars (prfx^name);
               return s_ctx *)
        | Some r ->
            assign (h :: get_tail ctxs) (VAR_NAME (prfx ^ name)) r in_fn t palcs 
      ) 
    | CT_PTR tt -> (
        cast_default_init ctxs t >>= fun v ->
        create_var ctxs (prfx ^ name) (Vhval (Vrval (prfx ^ name, v))) t
        >>= fun h -> match expr with
        | None | Some (LITERAL CNULL) -> 
            (* let cast_ptr_dcl ctxs in_fn palcs tt = malloc0 ctxs in_fn palcs 1 tt >>= fun (csv, _) -> return (csv, palcs) in *)
            (* return @@ (h :: get_tail ctxs, palcs) *)
            malloc0 (h :: get_tail ctxs) in_fn palcs 1 tt 
            >>= fun ((cs, v), pals) -> conv_to_int v
            >>= fun i -> assign cs (VAR_NAME (prfx ^ name)) (LITERAL (CINT (get_int i))) in_fn t palcs
            (* assign cs (VAR_NAME (prfx ^ name)) v in_fn t pals *)
            (* return (cs, pals) *)
        | Some r -> assign (h :: get_tail ctxs) (VAR_NAME (prfx ^ name)) r in_fn t palcs 
      )
    (* | CT_PTR tt -> (_

      ) *)
        (* >>= fun (s_ctx, pls) ->
           (* List.iter (fun ctx -> print_string @@ dbg_print ctx) s_ctx; *)
           let nahv =
             get_from_vars s_ctx (prfx ^ name) in_fn >>= function
             | Some v -> return v
             | None -> error "declare"
           in
           nahv >>= fun (t, a, hv) ->
           Hashtbl.add (get_cur_ctx ctxs).vars name
             (t, a, Vrval (name, get_val @@ Vhval hv));
           Hashtbl.replace (get_cur_ctx ctxs).heap a
             (Vrval (name, get_val @@ Vhval hv));
           Hashtbl.remove (get_cur_ctx ctxs).vars (prfx ^ name);
           (* List.iter (fun ctx -> print_string @@ dbg_print ctx) s_ctx; *)
           return (s_ctx, pls) *)

        (* | CT_PTR tt -> _ *)

        (* create_var ctxs (prfx^name) (Vhval (Vrval (prfx^name, v))) t >>= fun h ->
           match expr with
           | None -> return @@ (h :: get_tail ctxs)
               >>= fun s_ctx ->
               let nahv = get_from_vars s_ctx (prfx^name) >>= function | Some v -> return v | None -> error "" in
               nahv >>= fun (t, a, hv) ->
               Hashtbl.add (get_cur_ctx ctxs).vars name (t, a, Vrval (name, get_val @@ Vhval hv));
               Hashtbl.replace (get_cur_ctx ctxs).heap a (Vrval (name, get_val @@ Vhval hv));
               Hashtbl.remove (get_cur_ctx ctxs).vars (prfx^name);
               return s_ctx
           | Some r ->
               assign (h :: get_tail ctxs) (VAR_NAME (prfx^name)) r)
               >>= fun s_ctx ->
               let nahv = get_from_vars s_ctx (prfx^name) >>= function | Some v -> return v | None -> error "" in
               nahv >>= fun (t, a, hv) ->
               Hashtbl.add (get_cur_ctx ctxs).vars name (t, a, Vrval (name, get_val @@ Vhval hv));
               Hashtbl.replace (get_cur_ctx ctxs).heap a (Vrval (name, get_val @@ Vhval hv));
               Hashtbl.remove (get_cur_ctx ctxs).vars (prfx^name);
               return s_ctx *)

        (* | CT_INT | CT_CHAR | CT_PTR _ -> (
           cast_default_init ctxs t >>= fun v ->
           create_var ctxs name (Vhval (Vrval (name, v))) t >>= fun h ->
           match expr with
           | None -> return @@ (h :: get_tail ctxs)
           | Some r -> assign (h :: get_tail ctxs) (VAR_NAME name) r
           ) *)
    | CT_ARRAY (_, t') -> (
        cast_default_init0 ctxs t >>= fun v ->
        match expr with
        | None ->
            create_var ctxs (prfx ^ name)
              (Vhval
                 (Vrval
                    (prfx ^ name, Varraddress (t', (get_cur_ctx ctxs).free_addr))))
              t
            >>= fun c ->
            return @@ (c :: get_tail ctxs) >>= fun cs' -> return (cs', palcs)
            (* (Vhval (Vrval (name, Varraddress (get_cur_ctx ctxs).free_addr)))) _ *)
            (* return @@ (h :: get_tail ctxs) *)
        | Some r ->
            create_arr ctxs (prfx ^ name) v t >>= fun h ->
            assign (h :: get_tail ctxs) (VAR_NAME name) r in_fn t palcs)
    | CT_STRUCT tag -> (
        (* cast_default_init0 ctxs t >>= fun v ->

           match expr with
           | None ->
           create_struct ctxs name (Vhval (Vrval (name, Vstaddress (tag, (get_cur_ctx ctxs).free_addr)))) t >>= fun c -> return @@ c :: get_tail ctxs
             (* (Vhval (Vrval (name, Varraddress (get_cur_ctx ctxs).free_addr)))) _ *)
             (* return @@ (h :: get_tail ctxs) *)
           | Some r ->
           create_struct ctxs name v t >>= fun h -> assign (h :: get_tail ctxs) (VAR_NAME name) r in_fn) *)
        cast_default_init0 ctxs t
        >>= fun v ->
        create_struct ctxs (prfx ^ name) v t >>= fun h ->
        match expr with
        | None -> return @@ (h :: get_tail ctxs, palcs)
        | Some r ->
            assign (h :: get_tail ctxs) (VAR_NAME (prfx ^ name)) r in_fn t palcs
        )
    | CT_VOID -> error "void haven't values")
    >>= fun (s_ctx, pls) ->
    (* List.iter (fun ctx -> print_string @@ dbg_print ctx) s_ctx; *)
    let nahv =
      get_from_vars s_ctx (prfx ^ name) in_fn >>= function
      | Some v -> return v
      | None -> error "declare"
    in
    nahv >>= fun (t, a, hv) ->
    Hashtbl.add (get_cur_ctx ctxs).vars name
      (t, a, Vrval (name, get_val @@ Vhval hv));
    Hashtbl.replace (get_cur_ctx ctxs).heap a
      (Vrval (name, get_val @@ Vhval hv));
    Hashtbl.remove (get_cur_ctx ctxs).vars (prfx ^ name);
    (* List.iter (fun ctx -> print_string @@ dbg_print ctx) s_ctx; *)
    return (s_ctx, pls)

  and get_pos i = function [] -> i | _ :: cs -> get_pos (i + 1) cs

  and cut_by d ctxs =
    match ctxs with
    | [] -> []
    | _ :: cs when d > 0 -> cut_by (d - 1) cs
    | _ -> ctxs

  and assign (ctxs : exec_ctx list) l_expr r_expr (in_fn : bool) convt palcs =
    eval_expr ctxs in_fn convt palcs l_expr >>= fun (p, _) ->
    match snd p with
    (* function *)
    | Vhval (Vrval (n, _)) ->
        let var =
          get_from_vars ctxs n in_fn >>= function
          | Some v -> return v
          | None -> error "var undefined?"
        in
        var >>= fun (t, addr, _) ->
        (* print_string "\n\n";
           print_string @@ show_types t;
           print_string "\n";
           print_string @@ Int.to_string addr;
           print_string "\n\n"; *)
        eval_expr ctxs in_fn t (* convt  *) palcs r_expr
        >>= fun ((ctxs', r), pls) ->
        (* print_string "\n";
           List.iter (fun x -> print_string @@ dbg_print (x)) ctxs';
           print_string @@ dbg_print (get_cur_ctx ctxs');
           print_string "\n\n----\n"; *)
        return
        @@ {
             (get_cur_ctx ctxs) with
             last_value = (get_cur_ctx ctxs').last_value;
             free_addr =
               (get_cur_ctx ctxs').free_addr
               (* allocated = (get_cur_ctx ctxs').allocated; *)
               (* jump_stmt = (get_cur_ctx ctxs').jump_stmt; *);
           }
           :: get_tail ctxs
        >>= fun cs ->
        (* List.iter (fun x ->print_string "\n";print_string @@ dbg_print x; print_string "\n") cs; *)
        conv_t (get_val r) t >>= fun r' ->
        (* print_string "\n\n"; *)
        (* print_string @@ dbg_print @@ List.nth ctxs' old_p; *)
        (* print_string "\n\n"; *)

        (* List.iter (fun x ->
           print_string "\n";
           print_string @@ dbg_print x;
           print_string "\n";)
           ctxs'; *)
        (* eval_stmt ctxs @@ EXPRESSION r_expr >>= fun ctxs' ->  *)
        (* print_string  "\n\n";
           (* print_string @@ show_v_value r; *)
           print_string "\n";
           print_string @@ dbg_print (get_cur_ctx ctxs');
           print_string "\n\n"; *)
        rewrite_var cs n t r' addr >>= fun cs' -> return (cs', pls)
    (* rewrite_var ctxs n t (get_val r) addr *)
    (* rewrite_var (cut_by (new_p - old_p) ctxs') n t (get_val r) addr *)
    (* | Vhval (Vdval (_ad, Vmalloc (n, _v))) ->
        eval_expr ctxs in_fn r_expr >>= fun (ctxs', r) ->

        return
        @@ { (get_cur_ctx ctxs) with
             last_value = (get_cur_ctx ctxs').last_value;
             free_addr = (get_cur_ctx ctxs').free_addr;
               jump_stmt = (get_cur_ctx ctxs').jump_stmt;
            } :: get_tail ctxs
        >>= fun cs -> conv_v (get_val r) _v >>= fun r' ->
        Hashtbl.replace (get_cur_ctx cs).heap _ad (Vdval (_ad, get_val (Vmalloc (n, r'))));
        return cs
    *)
    | Vhval (Vdval (_ad, _v)) ->
        to_type _v >>= fun _convt ->
        eval_expr ctxs in_fn _convt palcs r_expr >>= fun ((ctxs', r), pls) ->
        return
        @@ {
             (get_cur_ctx ctxs) with
             last_value = (get_cur_ctx ctxs').last_value;
             free_addr = (get_cur_ctx ctxs').free_addr;
             jump_stmt = (get_cur_ctx ctxs').jump_stmt;
           }
           :: get_tail ctxs
        >>= fun cs ->
        conv_v (get_val r) _v >>= fun r' ->
        Hashtbl.replace (get_cur_ctx cs).heap _ad (Vdval (_ad, get_val r'));
        return (cs, pls)
        (* Hashtbl.replace (get_cur_ctx ctxs).heap _ad (Vdval (_ad, get_val r)); *)
        (* return ctxs *)
    | a -> error @@ show_v_value a
  (* return (ctxs, palcs) *)

  and eval_expr (ctxs : exec_ctx list) (in_fn : bool) convt (palcs : allocated)
      = function
    | VAR_NAME name -> (
        get_from_vars ctxs name in_fn >>= function
        | Some (_, _, v) -> return @@ ((ctxs, Vhval v), palcs)
        | None -> error @@ "Var undefined EXP" ^ name ^ (Bool.to_string in_fn)
        (* >>= fun (_, _, v) -> return v *))
    | LITERAL CNULL -> return @@ ((ctxs, Vnull), palcs)
    | LITERAL (CINT v) -> return @@ ((ctxs, Vint v), palcs)
    | LITERAL (CCHAR c) -> return @@ ((ctxs, Vchar c), palcs)
    | LITERAL CVOID -> return @@ ((ctxs, Vvoid), palcs)
    | LITERAL (CARRAY ls) ->
        List.fold_right
          (fun e acc ->
            acc >>= fun vs ->
            eval_expr ctxs in_fn convt palcs e >>= fun ((ctxs', v), _) ->
            return @@ (get_val v :: vs))
          ls (return [])
        >>= fun vs -> return @@ ((ctxs, Vvalues vs), palcs)
    | INITIALIZER es ->
        List.fold_right
          (fun e acc ->
            acc >>= fun vs ->
            eval_expr ctxs in_fn convt palcs e >>= fun ((ctxs', v), _) ->
            return @@ (get_val v :: vs))
          es (return [])
        >>= fun vs -> return @@ ((ctxs, Vvalues vs), palcs)
    | ADD (e1, e2) ->
        op ctxs _add e1 e2 in_fn convt palcs
        (* >>= fun v -> return (ctxs, v)     *)
    | SUB (e1, e2) ->
        op ctxs _sub e1 e2 in_fn convt palcs (* >>= fun v -> return (ctxs, v) *)
    | MUL (e1, e2) ->
        op ctxs _mul e1 e2 in_fn convt palcs (* >>= fun v -> return (ctxs, v) *)
    | DIV (e1, e2) ->
        op ctxs _div e1 e2 in_fn convt palcs (* >>= fun v -> return (ctxs, v) *)
    | MOD (e1, e2) ->
        op ctxs _mod e1 e2 in_fn convt palcs (* >>= fun v -> return (ctxs, v) *)
    | AND (e1, e2) ->
        op ctxs _and e1 e2 in_fn convt palcs (* >>= fun v -> return (ctxs, v) *)
    | OR (e1, e2) ->
        op ctxs _or e1 e2 in_fn convt palcs (* >>= fun v -> return (ctxs, v) *)
    | EQUAL (e1, e2) ->
        op ctxs _eq e1 e2 in_fn convt palcs (* >>= fun v -> return (ctxs, v) *)
    | NOT_EQUAL (e1, e2) ->
        op ctxs _neq e1 e2 in_fn convt palcs (* >>= fun v -> return (ctxs, v) *)
    | GTE (e1, e2) ->
        op ctxs _gte e1 e2 in_fn convt palcs (* >>= fun v -> return (ctxs, v) *)
    | GT (e1, e2) ->
        op ctxs _gt e1 e2 in_fn convt palcs (* >>= fun v -> return (ctxs, v) *)
    | LTE (e1, e2) ->
        op ctxs _lte e1 e2 in_fn convt palcs (* >>= fun v -> return (ctxs, v) *)
    | LT (e1, e2) ->
        op ctxs _lt e1 e2 in_fn convt palcs (* >>= fun v -> return (ctxs, v) *)
    | NOT e ->
        eval_expr ctxs in_fn convt palcs e >>= fun ((cts, v), pls) ->
        _not v >>= fun v' -> return ((cts, v'), pls)
    | INDEXER (n, e) ->
        let xable ctxs name i =
          get_from_vars ctxs name in_fn >>= function
          | Some (CT_ARRAY (_, t), _, Vrval (_, Varraddress (_, addr)))
          | Some (CT_PTR t, _, Vrval (_, Vaddress (_, addr))) -> (
              get_size t >>= fun s ->
              return @@ get_from_heap ctxs (addr + (i * s)) >>= function
              | Some v -> return @@ Vhval v
              | None -> return Vnull)
          | Some _ -> error "Not indexable"
          | None -> error "Var undefined"
        in
        eval_expr ctxs in_fn convt palcs e >>= fun ((cts, i), _) ->
        conv_to_int i >>= fun i' ->
        xable cts n @@ get_int i' >>= fun v' -> return ((cts, v'), palcs)
    | ACCESOR (e1, e2) -> (
        let strct_padding tag n bgn i =
          match get_from_struct_tags ctxs tag with
          | Some args -> (
              let rec pdng n args acc =
                match args with
                | (_, nn) :: _ when n = nn -> acc
                | (tt, _) :: tl ->
                    pdng n tl
                      ( acc >>= fun ac ->
                        sizeof ctxs tt
                        (* get_size tt*SIZEOF!!!!!!!!!!!!!!!!!!!!!!!!!** *)
                        >>=
                        fun x -> return @@ (x + ac) )
                | [] -> error "Nonexistent struct field"
              in
              pdng n args (return 0) >>= fun p ->
              match get_from_heap ctxs (bgn + p) with
              (*SIZE FOR IIIII!!!!!!!!!!!!!!!!!!!!!!!! *)
              | Some (Vdval (_, Vstructval (_, Varraddress (t', a')))) -> (
                  get_size t' >>= fun inc ->
                  match get_from_heap ctxs (a' + (i * inc)) with
                  | Some v -> return @@ Vhval v
                  | None -> error "A")
              | Some v -> return @@ Vhval v
              | None -> return Vnull)
          | None -> error "Struct undefined"
        in
        eval_expr ctxs in_fn convt palcs e1 >>= function
        | (_, Vhval (Vrval (_, Vstaddress (tag, a)))), pal
        | (_, Vhval (Vdval (_, Vstaddress (tag, a)))), pal 
        | (_, Vstructval (_, Vstaddress (tag, a))), pal -> (
            match e2 with
            | VAR_NAME n ->
                strct_padding tag n a 0 >>= fun v -> return ((ctxs, v), pal)
            (* | INDEXER (n, e) ->
                eval_expr ctxs in_fn e >>= fun (_, i) -> (match get_from_heap ctxs (addr + (get_int i) ) with | _  -> return _) *)
            | INDEXER (n, e) ->
                eval_expr ctxs in_fn convt palcs e >>= fun ((_, i), pal) ->
                (* strct_padding tag n (a + (get_int i)) >>= fun v -> return (ctxs, v) NEEW TO MV IN PDNG!!!!!!! *)
                strct_padding tag n a @@ get_int i >>= fun v ->
                return ((ctxs, v), pal)
                (* match get_from_heap ctxs (a + (get_int i)) with
                   | Some v -> return (ctxs, get_val @@ Vhval v)
                   | None -> error ""
                *)
            | _ ->
                error "AC for INDEXERR"
                (* e2 >>= fun *)
                (* return _ *))
        (* | (_, Vstructval (_, Varraddress a)) -> (
            match e2 with
            | INDEXER (n, e) -> (
                eval_expr ctxs in_fn e >>= fun (_, i) ->
                match get_from_heap ctxs (a + (get_int i) ) with
                | Some v -> return (ctxs, get_val @@ Vhval v)
                | None -> return (ctxs, Vnull))
            | _ -> error "") *)
        | (_, xx), _ -> error @@ "Unaccessorable" ^ show_v_value xx)
    | DEREFERENCE e -> (
        eval_expr ctxs in_fn convt palcs e >>= fun ((cs, v), pals) -> conv_to_int @@ get_val v 
        >>= fun v' -> match get_from_heap cs (get_int @@ v') with 
        | Some v'' -> return ((cs, Vhval v''), pals)
        | _ -> error ""
      )
    (* | DEREFERENCE e -> (
        let h_val ctxs a = get_from_heap ctxs a >>= function
          | Some () -> return _
          | _ -> return _
        in
        eval_expr ctxs e >>= fun (cts, _a) -> get_from_heap cts _a) *)
    (* | ACCESOR (e1, e2) ->
        match e1 with
        | VAR_NAME n | INDEXER (n, _) | *)
    | FUNC_CALL (n, vals) -> (
        match n with
        | "malloc" -> (
            (* malloc ((make_dep_ctx (get_cur_ctx ctxs) () ) :: ctxs) in_fn vals *)
            match vals with
            | [ v ] -> (
                eval_expr ctxs in_fn convt palcs v >>= fun ((_, cnt), pal) ->
                (* print_string "\n";
                   print_string @@ show_types convt;
                   print_string "\n"; *)
                match convt with
                | CT_PTR ctt ->
                    malloc0
                      (make_dep_ctx (get_cur_ctx ctxs) () :: ctxs)
                      in_fn pal (get_int cnt) ctt
                | ttt -> error @@ "PPP" ^ " " ^ show_types ttt
                (* @@ CT_STRUCT "mSt2" *))
            | _ -> error "")
        (* | "sizeof" -> ( match vals with
            | [v] -> eval_expr ctxs v
                >>= fun (cs, v') -> return (cs, v')
            | _ -> error "") *)
        | "main" ->
            main (make_dep_ctx (get_cur_ctx ctxs) () :: ctxs) convt palcs
        | _ ->
            (* let old_tl = get_tail ctxs in *)
            eval_fun
              (make_dep_ctx (get_cur_ctx ctxs) () :: ctxs)
              convt palcs n vals
            >>= fun ((cs, x), pls) ->
            (* print_string @@ "\n\n EHRE: " ^ n ^ "\n";
               print_string @@ dbg_print @@ get_cur_ctx cs;
               print_string "\n\n"; *)
            return ((cs, x), pls))
    | _ -> error "expr"

  and main ctxs convt palcs =
    let stmts =
      match get_from_functions ctxs "main" with
      | Some f -> return f
      | None -> error "Function undeclared"
    in
    let rec blk ctxs (in_fn : bool) pls = function
      | [] -> return @@ (ctxs, pls)
      | st :: sts -> (
          eval_stmt ctxs in_fn convt pls st >>= fun (new_ctx, pls') ->
          let cur_ctx = get_cur_ctx new_ctx in
          match cur_ctx.jump_stmt with
          | None -> blk new_ctx in_fn pls' sts
          | Return _ | Break | Next -> return (new_ctx, pls'))
    in
    stmts >>= fun (_, _, vs) ->
    blk ctxs false palcs vs >>= fun (ctxs', pls) ->
    match (get_cur_ctx ctxs').jump_stmt with
    | Return _ ->
        return
          ( ( get_cur_ctx ctxs' :: get_prev_tl ctxs,
              (get_cur_ctx ctxs').last_value ),
            pls )
    | _ -> error "Unexpected jump statement"

  and malloc0 ctxs (in_fn : bool) (palcs : allocated) size tt =
    let s' =
      sizeof ctxs tt >>= fun sot ->
      if size >= sot then return size else return sot
    in
    let adr = (get_cur_ctx ctxs).free_addr in
    let upd_allocs alctd ctxs =
      List.fold_right
        (fun c acc ->
          acc >>= fun ac -> return @@ ({ c with allocated = alctd } :: ac))
        ctxs (return [])
    in
    s' >>= fun s ->
    (* return
       @@ { (get_cur_ctx ctxs) with
            allocated = (adr, adr + s) :: (get_cur_ctx ctxs).allocated
          } :: get_tail ctxs *)
    List.fold_right
      (fun c acc ->
        acc >>= fun ac ->
        return
        @@ { c with allocated = (adr, adr + s) :: (get_cur_ctx ctxs).allocated }
           :: ac)
      ctxs (return [])
    >>= fun ctxs' ->
    (* List.iter (fun x ->print_string "\n";print_string @@ dbg_print x; print_string "\n") ctxs'; *)
    sizeof ctxs tt >>= fun sot ->
    cast_default_init0 ctxs @@ CT_ARRAY (s / sot, tt) >>= function
    | Vvalues vs ->
        List.fold_left
          (fun c v ->
            match v with
            | Vstructval (n, v') ->
                to_type v' >>= fun t ->
                c >>= fun c ->
                cast_default_dep_v c t n (CT_STRUCT "tag") >>= fun x ->
                return [ x ]
            | _ ->
                to_type v >>= fun t ->
                c >>= fun c ->
                cast_default_dep_v c t "" (CT_ARRAY (0, CT_INT)) >>= fun x ->
                return [ x ])
          (return @@ ctxs) vs
        >>= fun x ->
        return @@ get_cur_ctx x >>= fun h ->
        (* print_string "\n"; *)
        (* print_string @@ dbg_print h; *)
        (* print_string @@ Int.to_string adr; *)
        (* print_string "\n";
           print_string @@ Int.to_string @@ adr + s; *)
        (* print_string "\n"; *)
        (* print_string h; *)
        (* List.iter (fun x ->print_string "\n";print_string @@ dbg_print x; print_string "\n") (h :: get_prev_tl ctxs'); *)
        return
          ( (h :: get_prev_tl ctxs, Vaddress (tt, adr)),
            (adr, adr + s - 1) :: palcs )
        (* return @@ ((h :: get_prev_tl ctxs, Vaddress adr), (adr, adr + s) :: palcs), (adr, adr + s) :: palcs) *)
    | _ -> error "MMM"
  (* create_arr ctxs "." v @@ CT_ARRAY (1, CT_INT) >>= fun h ->  *)

  (* cast_default_init ctxs CT_INT  >>= fun v ->
     create_var ctxs ("") (Vhval (Vrval ("", v))) CT_INT >>= fun h -> *)
  (* cast_default_init0 ctxs (CT_STRUCT "mSt2") >>= fun v ->
     create_struct ctxs "mSt2" v (CT_STRUCT "mSt2") >>= fun h -> *)
  (* return @@ (h :: get_prev_tl ctxs, Vaddress adr ) *)

  and _add v1 v2 =
    let vv =
      match (v1, v2) with
      | Vaddress (tt, _), _ | _, Vaddress (tt, _) ->
          conv_to_addr tt v1 >>= fun v1' ->
          conv_to_addr tt v2 >>= fun v2' -> return (v1', v2')
      | _ ->
          conv_to_int v1 >>= fun v1' ->
          conv_to_int v2 >>= fun v2' -> return (v1', v2')
    in
    vv >>= fun (vv1, vv2) ->
    (* let vv1 = conv_to_int v1 in
       let vv2 = conv_to_int v2 in *)
    (* vv1 >>= fun n1 ->
       vv2 >>= fun n2 -> *)
    match (vv1, vv2) with
    | Vint vn1, Vint vn2 -> return @@ Vint (vn1 + vn2)
    | Vaddress (tt, vn1), Vaddress (_, vn2) -> return @@ Vaddress (tt, vn1 + vn2)
    | _ -> error "Invalid operands"

  and _sub v1 v2 =
    let vv1 = conv_to_int v1 in
    let vv2 = conv_to_int v2 in
    vv1 >>= fun n1 ->
    vv2 >>= fun n2 ->
    match (n1, n2) with
    | Vint vn1, Vint vn2 -> return @@ Vint (vn1 - vn2)
    | _ -> error "Invalid operands"

  and _mul v1 v2 =
    let vv1 = conv_to_int v1 in
    let vv2 = conv_to_int v2 in
    vv1 >>= fun n1 ->
    vv2 >>= fun n2 ->
    match (n1, n2) with
    | Vint vn1, Vint vn2 -> return @@ Vint (vn1 * vn2)
    | _ -> error "Invalid operands"

  and _div v1 v2 =
    let vv1 = conv_to_int v1 in
    let vv2 = conv_to_int v2 in
    vv1 >>= fun n1 ->
    vv2 >>= fun n2 ->
    match (n1, n2) with
    | Vint vn1, Vint vn2 when vn2 <> 0 -> return @@ Vint (vn1 / vn2)
    | _ -> error "Invalid operands"

  and _mod v1 v2 =
    let vv1 = conv_to_int v1 in
    let vv2 = conv_to_int v2 in
    vv1 >>= fun n1 ->
    vv2 >>= fun n2 ->
    match (n1, n2) with
    | Vint vn1, Vint vn2 when vn2 <> 0 -> return @@ Vint (vn1 mod vn2)
    | _ -> error "Invalid operands"

  and bool_to_num e = if e then 1 else 0

  and _and v1 v2 =
    let vv1 = conv_to_int v1 in
    let vv2 = conv_to_int v2 in
    vv1 >>= fun n1 ->
    vv2 >>= fun n2 ->
    match (n1, n2) with
    | Vint o1, Vint o2 -> return @@ Vint (bool_to_num (o1 > 0 && o2 > 0))
    | _ -> error "Invalid operands"

  and _or v1 v2 =
    let vv1 = conv_to_int v1 in
    let vv2 = conv_to_int v2 in
    vv1 >>= fun n1 ->
    vv2 >>= fun n2 ->
    match (n1, n2) with
    | Vint o1, Vint o2 -> return @@ Vint (bool_to_num (o1 > 0 || o2 > 0))
    | _ -> error "Invalid operands"

  and _lt v1 v2 =
    let vv1 = conv_to_int v1 in
    let vv2 = conv_to_int v2 in
    vv1 >>= fun n1 ->
    vv2 >>= fun n2 ->
    match (n1, n2) with
    | Vint o1, Vint o2 -> return @@ Vint (bool_to_num (o1 < o2))
    | _ -> error "Unknown types"

  and _gt v1 v2 =
    let vv1 = conv_to_int v1 in
    let vv2 = conv_to_int v2 in
    vv1 >>= fun n1 ->
    vv2 >>= fun n2 ->
    match (n1, n2) with
    | Vint o1, Vint o2 -> return @@ Vint (bool_to_num (o1 > o2))
    | _ -> error "Unknown types"

  and _lte v1 v2 =
    let vv1 = conv_to_int v1 in
    let vv2 = conv_to_int v2 in
    vv1 >>= fun n1 ->
    vv2 >>= fun n2 ->
    match (n1, n2) with
    | Vint o1, Vint o2 -> return @@ Vint (bool_to_num (o1 <= o2))
    | _ -> error "Unknown types"

  and _gte v1 v2 =
    let vv1 = conv_to_int v1 in
    let vv2 = conv_to_int v2 in
    vv1 >>= fun n1 ->
    vv2 >>= fun n2 ->
    match (n1, n2) with
    | Vint o1, Vint o2 -> return @@ Vint (bool_to_num (o1 >= o2))
    | _ -> error "Unknown types"

  and _not v =
    let vv1 = conv_to_int v in
    vv1 >>= fun n ->
    match n with
    | Vint o1 -> return @@ Vint (if not (o1 > 0) then 1 else 0)
    | _ -> error "Unknown types"

  and _eq v1 v2 =
    let vv1 = conv_to_int v1 in
    let vv2 = conv_to_int v2 in
    vv1 >>= fun n1 ->
    vv2 >>= fun n2 ->
    match (n1, n2) with
    | Vint o1, Vint o2 -> return @@ Vint (bool_to_num (o1 == o2))
    | _ -> error "Unknown types"

  and _neq v1 v2 =
    let vv1 = conv_to_int v1 in
    let vv2 = conv_to_int v2 in
    vv1 >>= fun n1 ->
    vv2 >>= fun n2 ->
    match (n1, n2) with
    | Vint o1, Vint o2 -> return @@ Vint (bool_to_num (o1 == o2))
    | _ -> error "Unknown types"

  and get_val = function
    | Vhval (Vdval (_, Vmalloc (_, v))) -> v
    | Vhval (Vrval (_, v)) | Vhval (Vdval (_, v)) -> v
    | v -> v

  and op (ctxs : exec_ctx list) opp e1 e2 in_fn convt palcs =
    eval_expr ctxs in_fn convt palcs e1 >>= fun ((cs, v1), pls) ->
    eval_expr cs in_fn convt pls e2 >>= fun ((cts, v2), pls') ->
    opp (get_val @@ v1) (get_val @@ v2) >>= fun v' -> return ((cts, v'), pls')

  and conv_for_op = function
    | Vint v -> return @@ Vint v
    | Vchar v -> return @@ Vint (Char.code v)
    | Vaddress v -> return @@ Vaddress v
    | _ -> return @@ Vint 0

  and get_int = function Vint v -> v | _ -> 0
  (* function [] -> [] | _ :: tl -> tl *)

  and eval_block_fn ctxs (in_fn : bool) (convt : types) palcs = function
    | [] -> return @@ (get_tail ctxs, palcs) (*delete from heap locals!!!!!!*)
    | st :: sts -> (
        (* print_string "\n";
           print_string @@ show_allocated palcs;
           print_string "\n"; *)
        let rec rm ctx i n =
          (* print_string "\n";
             print_string @@ Int.to_string i;
             print_string "\n"; *)
          if i <= n then
            if
              (* print_string "\n";
                 print_string @@ Int.to_string i;
                 print_string "\n";
                 print_string @@ Bool.to_string @@ b_srch i palcs;
                 print_string "\n";
                 print_string "\n"; *)
              not @@ b_srch i palcs
            then (
              Hashtbl.remove ctx.heap i;
              rm ctx (i + 1) n)
            else rm ctx (i + 1) n
          else ()
        in
        eval_stmt ctxs in_fn convt palcs st >>= fun (new_ctx, pls) ->
        let cur_ctx = get_cur_ctx new_ctx in
        match cur_ctx.jump_stmt with
        | None -> eval_block_fn new_ctx in_fn convt pls sts
        | Return _ | Break | Next ->
            rm (get_cur_ctx ctxs) (get_cur_ctx ctxs).pack_addr
              (get_cur_ctx ctxs).free_addr;

            return
            @@ ( {
                   (get_prev_env new_ctx) with
                   free_addr =
                     (match List.rev @@ List.sort compare palcs with
                     | _ :: p :: _ -> snd p + 1
                     | _ -> cur_ctx.pack_addr);
                   (* free_addr = cur_ctx.pack_addr; *)
                   (* cur_ctx.pack_addr; *)
                   (* if (List.length pls = 1) then (cur_ctx.pack_addr) else (match pls with | _ :: tl -> (snd @@ List.hd @@ List.rev @@ List.sort compare tl) + 1 | _ -> 0); *)
                   (* ((snd @@ List.hd @@ List.rev @@ List.sort compare pls) + 1); *)

                   (* free_addr = cur_ctx.free_addr; *)
                   (*!!!!!!!!!!!!!!!!!!!LST*)
                   jump_stmt = cur_ctx.jump_stmt;
                   last_value = cur_ctx.last_value;
                 }
                 :: get_prev_tl ctxs,
                 pls )
        (* >>= fun cs'' -> return cs'' *))

  and get_vval000 = function
    | Vhval (Vrval (_, v)) | Vhval (Vdval (_, v)) -> v
    | v -> v

  and eval_fun ctxs (convt : types) (palcs : allocated) name vals =
    (* let f_ctxs args = List.map2 (fun v a -> ) vals args in *)
    let stmts =
      match get_from_functions ctxs name with
      | Some f -> return f
      | None -> error "Function undeclared"
    in
    (*let avs = List.map2 (fun (t, n) v -> ) args vals in *)
    stmts >>= fun (_, args, vs) ->
    List.fold_right2
      (fun (CARGS (t, n)) v d -> 
      d >>= fun ds -> return @@ (VAR_DECL (n, t, Some v) :: ds))
      args vals (return [])
    >>= fun ds ->
    eval_stmt ctxs true convt palcs @@ T_BLOCK (ds @ vs) >>= fun (ctxs', pls) ->
    match (get_cur_ctx ctxs').jump_stmt with
    | Return _ ->
        (*
             print_string "\n\n";
             print_string @@ dbg_print @@ get_cur_ctx ctxs;
             print_string "\n\n"; *)
        return
          ( ( (* ctxs' *)
              {
                (* (get_cur_ctx ctxs) *)
                (get_prev_env ctxs) with
                free_addr = (get_cur_ctx ctxs').free_addr;
                last_value =
                  (get_cur_ctx ctxs').last_value
                  (* heap = (get_cur_ctx ctxs').heap; *);
              }
              :: get_prev_tl ctxs
              (* get_tail ctxs *),
              (get_cur_ctx ctxs').last_value ),
            pls )
    | _ -> error "Unexpected jump statement"

  (* return @@ Vint 0 *)
  (* let test11 =
         eval_stmt ((() |> make_exec_ctx) :: []) @@ VAR_DECL ("b", CT_INT, Some (LITERAL (CINT 10) ))
         (* >>= fun xx -> assign xx (VAR_NAME "b") (LITERAL (CINT 10))  *)
         >>= fun x -> return @@ List.fold_left (fun acc xx -> dbg_print (xx) :: acc) [] x

         (* Some (LITERAL (CINT 10)) *)

     let test10 =
       eval_stmt ((() |> make_exec_ctx) :: []) @@ VAR_DECL ("b", CT_ARRAY (5,CT_INT), None)
       >>= fun x -> return @@ List.fold_left (fun acc xx -> dbg_print (xx) :: acc) [] x *)

  (* let test11 =
     eval_stmt ((() |> make_exec_ctx) :: [])
     @@ EXPRESSION (FUNC_CALL ("malloc", [LITERAL (CINT 8)]))
     >>= fun x ->
     return
     @@ List.fold_left (fun acc xx -> dbg_print xx :: acc) [] x *)

  let testtt =
    (* max_int *)
    (* b_srch 13   *)
    match
      List.rev @@ List.sort compare [ (1, 2); (4, 8); (max_int, max_int) ]
    with
    | _ :: p :: _ -> snd p
    | _ -> 0

  let test13 =
    declare_struct (make_exec_ctx ())
    @@ (* TOP_STRUCT_DECL ("mSt0", [CARGS (CT_ARRAY (2,CT_INT), "at")]) *)
    TOP_STRUCT_DECL
      ( "mSt0",
        [
          (* CARGS (CT_ARRAY(5,CT_INT), "atarr0"); *)
          CARGS (CT_INT, "at0");
          CARGS (CT_CHAR, "at1");
        ] )
    >>= fun ctx ->
    declare_struct ctx
    @@ TOP_STRUCT_DECL
         ( "mSt2",
           [
             (* CARGS (CT_ARRAY(1, CT_STRUCT "mSt0"), "at"); *)
             CARGS (CT_STRUCT "mSt0", "at2");
             (* CARGS (CT_ARRAY (2,CT_INT), "attt") *)
             CARGS (CT_INT, "att2");
           ] )
    >>= fun ctx ->
    declare_struct ctx
    @@ TOP_STRUCT_DECL
         ( "mSt100",
           [
             (* CARGS (CT_ARRAY(5, CT_STRUCT "mSt0"), "at"); *)
             (* CARGS (CT_ARRAY (2,CT_INT), "attt"); *)

             (* CARGS (CT_ARRAY (1,CT_STRUCT "mSt0"), "att2"); *)

             (* CARGS (CT_INT, "att1"); *)
             (* CARGS (CT_INT, "att2") *)

             (* CARGS (CT_STRUCT "mSt2", "at100"); *)
             CARGS (CT_INT, "data");
             CARGS (CT_PTR (CT_STRUCT "mSt100"), "next");
           ] )
    >>= fun ctx ->
    declare_struct ctx
    @@ TOP_STRUCT_DECL
         ( "node",
           [
             (* CARGS (CT_ARRAY(5, CT_STRUCT "mSt0"), "at"); *)
             (* CARGS (CT_ARRAY (2,CT_INT), "attt"); *)

             (* CARGS (CT_ARRAY (1,CT_STRUCT "mSt0"), "att2"); *)

             (* CARGS (CT_INT, "att1"); *)
             (* CARGS (CT_INT, "att2") *)

             (* CARGS (CT_STRUCT "mSt2", "at100"); *)
             CARGS (CT_INT, "data");
             CARGS (CT_PTR (CT_STRUCT "node"), "next");
             
             (* CARGS (CT_INT, "srata"); *)

             (* CARGS (CT_PTR (CT_STRUCT "node"), "next"); *)
           ] )
    >>= fun ctx ->
    declare_struct ctx
    @@ TOP_STRUCT_DECL
         ( "list",
           [
             CARGS (CT_PTR (CT_STRUCT "node"), "head");
           ] 
         )
    >>= fun ctx ->
    declare_struct ctx
    @@ TOP_STRUCT_DECL
         ( "node0",
           [
             (* CARGS (CT_ARRAY(5, CT_STRUCT "mSt0"), "at"); *)
             (* CARGS (CT_ARRAY (2,CT_INT), "attt"); *)

             (* CARGS (CT_ARRAY (1,CT_STRUCT "mSt0"), "att2"); *)

             (* CARGS (CT_INT, "att1"); *)
             (* CARGS (CT_INT, "att2") *)

             (* CARGS (CT_STRUCT "mSt2", "at100"); *)
             CARGS (CT_INT, "data0");
             CARGS (CT_INT, "srata0");

             (* CARGS (CT_PTR (CT_STRUCT "node"), "next"); *)
           ] )
    >>= fun ctx ->
    declare_fun ctx
    @@ TOP_FUNC_DECL
         ( CT_INT,
           "fn",
           [],
           T_BLOCK
             [
               (* VAR_DECL ("aab", CT_INT,
                    Some (FUNC_CALL("malloc", [LITERAL (CINT 5)] ))
                  ); *)
               (* VAR_DECL ("tstst", CT_STRUCT "mSt2",
                    (Some (INITIALIZER [INITIALIZER [ INITIALIZER [ LITERAL (CINT 10)] ]]) )
                  );
               *)
               RETURN
                 (LITERAL
                    (CINT 10)
                    (* VAR_NAME "a" *)
                    (* FUNC_CALL("malloc", [LITERAL (CINT 5)] )  *));
             ] )
    >>= fun ctx ->
    declare_fun ctx
    @@ TOP_FUNC_DECL
         ( CT_INT,
           "tt",
           [],
           T_BLOCK
             [
               VAR_DECL
                 ( "pt",
                   CT_PTR (CT_STRUCT "mSt2"),
                   Some (FUNC_CALL ("malloc", [ LITERAL (CINT 17) ])) );
               VAR_DECL ("pt", CT_INT, Some (LITERAL (CINT 17)));
               RETURN ((* LITERAL (CINT 10) *)
                         FUNC_CALL ("fn", []));
             ] )
    >>= fun ctx ->
    declare_fun ctx
    @@ TOP_FUNC_DECL
         ( CT_INT,
           "addHead",
           [CARGS (CT_PTR (CT_STRUCT "list"), "list1"); CARGS (CT_INT, "value")],
           T_BLOCK
             [
               (* VAR_DECL ("node", CT_PTR (CT_STRUCT "node"), Some (FUNC_CALL ("malloc", [LITERAL (CINT 1)])));
               T_ASSIGN (ACCESOR (DEREFERENCE (VAR_NAME "node"), VAR_NAME "data"), VAR_NAME "value");
               T_ASSIGN (ACCESOR (DEREFERENCE (VAR_NAME "node"), VAR_NAME "next"), ACCESOR (DEREFERENCE (VAR_NAME "list"), VAR_NAME "head"));
               T_ASSIGN (ACCESOR (DEREFERENCE (VAR_NAME "list"), VAR_NAME "head"), VAR_NAME "node"); *)


               RETURN (
                          LITERAL (CINT 10)
                         (* FUNC_CALL ("fn", []) *)
                      );
             ] )
    >>= fun ctx ->
    declare_fun ctx
    @@ TOP_FUNC_DECL
         ( CT_INT,
           "main",
           [],
           T_BLOCK
             [
               VAR_DECL ("list0", CT_PTR (CT_STRUCT "list"), Some (FUNC_CALL ("malloc", [LITERAL (CINT 1)])));


               (* VAR_DECL ("node", CT_PTR (CT_STRUCT "node"), Some (FUNC_CALL ("malloc", [LITERAL (CINT 1)])));
               T_ASSIGN (ACCESOR (DEREFERENCE (VAR_NAME "node"), VAR_NAME "data"), LITERAL (CINT 100));
               T_ASSIGN (ACCESOR (DEREFERENCE (VAR_NAME "node"), VAR_NAME "next"), ACCESOR (DEREFERENCE (VAR_NAME "list"), VAR_NAME "head"));
               T_ASSIGN (ACCESOR (DEREFERENCE (VAR_NAME "list"), VAR_NAME "head"), VAR_NAME "node"); *)

               EXPRESSION (FUNC_CALL ("addHead", [VAR_NAME "list0"; LITERAL (CINT 100)]));

               (* VAR_DECL ("pt", CT_PTR (CT_STRUCT "node"), Some (LITERAL (CNULL))); *)
               (* VAR_DECL ("tst", CT_STRUCT "node", Some (DEREFERENCE (VAR_NAME "pt"))); *)



               (* VAR_DECL ("tst0", CT_INT, Some (ACCESOR (DEREFERENCE (VAR_NAME "pt"), VAR_NAME "data"))); *)
               (* VAR_DECL ("tst", CT_PTR (CT_STRUCT "node"), Some (FUNC_CALL ("malloc", [LITERAL (CINT 1)]))); *)
               (* VAR_DECL ("tst0", CT_STRUCT "node0", Some (VAR_NAME "tst")); *)
               (* VAR_DECL ("tst1", CT_STRUCT "node", Some (DEREFERENCE (VAR_NAME "tst"))); *)
               
               (* T_ASSIGN (VAR_NAME "pt", FUNC_CALL ("malloc", [LITERAL (CINT 5)])); *)

               (* VAR_DECL ("tst", ) *)
               (* VAR_DECL ("tst", CT_STRUCT "node", ) *)
               (*
                                VAR_DECL ("tst", CT_STRUCT "node",
                                  (* None *)
                                  Some (
                                  INITIALIZER [LITERAL (CINT 10); LITERAL (CINT 100)])
                                );
                                T_ASSIGN (ACCESOR (VAR_NAME "tst", VAR_NAME "next"), FUNC_CALL ("malloc", [LITERAL (CINT 5)])); *)

               (* VAR_DECL ("a", CT_ARRAY (1,CT_INT), Some (INITIALIZER [ LITERAL (CINT 10) ]));
                  T_ASSIGN (INDEXER ("a", LITERAL (CINT 0)), LITERAL (CINT 100)); *)

               (*
                  VAR_DECL ("a", CT_INT, Some (LITERAL (CINT 100)));
                  (* T_ASSIGN (VAR_NAME "a", LITERAL (CINT 100)); *)
                  VAR_DECL ("arr", CT_ARRAY (1,CT_INT),
                    Some (INITIALIZER [LITERAL (CINT 10)] ));
                  T_ASSIGN (INDEXER ("arr", LITERAL (CINT 0)), VAR_NAME "a"); *)
               RETURN (LITERAL (CINT 0) (* FUNC_CALL("fn", [] )  *));
             ] )
    >>= fun ctx ->
    (* cast_default_struct_init [ctx] "mSt100" *)
    (* cast_default_arr_init [ctx] 1 @@ CT_STRUCT "mSt0" *)
    eval_stmt [ ctx ] false CT_INT [ (max_int, max_int) ]
    @@ EXPRESSION (FUNC_CALL ("main", []))
    (* sizeof [ctx] @@ CT_STRUCT "mSt2" *)
    (* @@ T_BLOCK ([
         VAR_DECL ("tst", CT_ARRAY (2, CT_INT), None);
         VAR_DECL ("itst", CT_INT, Some (INDEXER ("tst", LITERAL (CINT 0))))
       ]) *)
    (* @@ T_BLOCK ([ VAR_DECL ("tst", CT_STRUCT "mSt100", None) ]) *)
    (* @@ EXPRESSION (FUNC_CALL ("main", [])) *)
    (* @@ VAR_DECL ("arr", CT_ARRAY (2, CT_INT), Some (
                INITIALIZER [LITERAL (CINT 10); LITERAL (CINT 20)])
              ); *)
    >>=
    fun (x, pas) ->
    return @@ List.fold_right (fun xx acc -> dbg_print xx pas :: acc) x []

  (*
   List.iter (fun x -> print_string (x ^ "\n_______________________\n"))  @@  Result.get_ok Interpreter.E.test13;; 
*)
end

module E = Eval (Result)
