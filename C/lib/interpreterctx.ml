open Ast
open Parser

type h_value = Vrval of string * v_value | Vdval of int * v_value

and v_value =
  | Vhval of h_value
  | Vint of int
  | Vchar of char
  | Vaddress of (types * int)
  | Vstaddress of (string * int)
  | Varraddress of (types * int)
  | Vstructval of string * v_value
  | Vvoid
  | Vnull (* | Vptr of v_value *)
  | Vinitializer of expr list
  | Vmalloc of int * v_value
  | Vvalues of v_value list
  | Vtype of types
[@@deriving show { with_path = false }]

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

and vars = (string, types * int * h_value) Ast.Hashtbl.t
[@@deriving show { with_path = false }]

and heap = (int, h_value) Ast.Hashtbl.t [@@deriving show { with_path = false }]

and functions = (string, types * args list * statements list) Ast.Hashtbl.t
[@@deriving show { with_path = false }]

and struct_tags = (string, (types * string) list) Ast.Hashtbl.t
[@@deriving show { with_path = false }]

and jump_stmt = None | Break | Next | Return of v_value
[@@deriving show { with_path = false }]

and allocated = (int * int) list [@@deriving show { with_path = false }]

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
  ^ "\npack_addr: "
  ^ Int.to_string ctx.pack_addr
  ^ "\nfree_addr: "
  ^ Int.to_string ctx.free_addr
  ^ "\nlast_value: "
  ^ show_v_value ctx.last_value
  ^ "\njump_stmt: "
  ^ show_jump_stmt ctx.jump_stmt
  ^ "\nallocated: "
  ^ show_allocated (List.sort compare palcs)
  ^ "\nheap: \n" ^ show_heap ctx.heap ^ "\nlocal_vars: " ^ show_vars ctx.vars

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

  let get_size = function
    | CT_INT | CT_PTR _ | CT_ARRAY _ | CT_STRUCT _ -> return 4
    | CT_CHAR -> return 1
    | CT_VOID -> error "Void haven't size"

  let get_from_struct_tags ctx tag = Ast.Hashtbl.find_opt ctx.struct_tags tag

  let rec sizeof ctx t =
    match t with
    | CT_INT | CT_PTR _ | CT_CHAR _ | CT_VOID _ -> get_size t
    | CT_ARRAY (size, tt) -> sizeof ctx tt >>= fun x -> return @@ (x * size)
    | CT_STRUCT tag -> (
        match get_from_struct_tags ctx tag with
        | Some ps ->
            List.fold_left
              (fun acc (tt, _) ->
                acc >>= fun ac ->
                sizeof ctx tt >>= fun inc -> return @@ (ac + inc))
              (return 0) ps
            >>= fun x ->
            get_size @@ CT_STRUCT "tag" >>= fun inc -> return @@ (x + inc)
        | None -> error "struct undeclared")

  let add_in_vars ctx name addr v t =
    match Hashtbl.find_opt ctx.vars name with
    | Some _ -> error @@ "name" ^ name ^ "already using"
    | None ->
        Ast.Hashtbl.add ctx.vars name (t, addr, v);
        return ctx

  let add_in_heap ctx addr v t =
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

  let get_from_functions ctx name = Ast.Hashtbl.find_opt ctx.functions name

  let get_from_heap ctx addr = Ast.Hashtbl.find_opt ctx.heap addr

  let rec get_from_vars ctx name = return @@ Ast.Hashtbl.find_opt ctx.vars name

  let create_var ctx name (v : v_value) t =
    match v with
    | Vhval (Vrval (_n, _v)) ->
        let ctx = ctx in
        add_in_vars ctx name ctx.free_addr (Vrval (_n, _v)) t >>= fun ctx ->
        add_in_heap ctx ctx.free_addr (Vrval (_n, _v)) t
    | _ -> error "create_var"

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

  let get_val = function
    | Vhval (Vdval (_, Vmalloc (_, v))) -> v
    | Vhval (Vrval (_, v)) | Vhval (Vdval (_, v)) -> v
    | v -> v

  let rec conv_to_addr tt = function
    (* | Vmalloc (_, v) -> conv_to_addr v *)
    | Vstructval (_, Vint v) | Vint v -> return @@ Vaddress (tt, v)
    | Vstructval (_, Vchar v) | Vchar v -> return @@ Vaddress (tt, Char.code v)
    | Vstructval (_, Vaddress v) | Vaddress v -> return @@ Vaddress v
    | Vnull -> return @@ Vaddress (tt, 0)
    | Varraddress (_, v) -> return @@ Vaddress (tt, v)
    (* | v -> return v *)
    | v -> error @@ "Adress expected" ^ show_v_value v

  let rec conv_to_int v =
    match get_val v with
    (* function *)
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

  let get_int = function Vint v -> v | _ -> 0

  let rec eval_stmt (ctx : exec_ctx) (in_fn : bool) (convt : types)
      (palcs : allocated) = function
    | VAR_DECL (name, t, expr) ->
        declare ctx name t expr in_fn convt palcs >>= fun (ctx', pls) ->
        return (ctx', pls)
    | EXPRESSION (FUNC_CALL (n, vs)) ->
        eval_expr ctx in_fn convt palcs @@ FUNC_CALL (n, vs)
        >>= fun ((ctxs', lv), pls) -> return (ctxs', pls)
    | RETURN e ->
        eval_expr ctx in_fn convt palcs e >>= fun ((ctxs', v), pls) ->
        return
          {
            ctx with
            jump_stmt = Return v;
            last_value = get_val v;
            free_addr = ctxs'.free_addr;
          }
        >>= fun cs -> return (cs, pls)
    | T_BLOCK stmts ->
        eval_block_fn ctx in_fn convt palcs stmts >>= fun (x, xx) -> 
        print_string @@ "\n" ^ dbg_print x xx ^ "\n";
        return (x, xx)
    | IF_ELSE (e, if_blk, else_blk) ->
        eval_expr ctx in_fn convt palcs e >>= fun ((ct, bv), pals) ->
        let stmts blk = match blk with T_BLOCK stmts -> stmts | _ -> [] in
        let old_pcka = ctx.pack_addr in
        let eval_ifelse blk = 
          eval_block_fn
            { ctx with pack_addr = ctx.free_addr }
            in_fn convt palcs blk
          >>= fun (c, ps) ->
          return ({ c with free_addr = c.pack_addr; pack_addr = old_pcka }, ps)
        in
        (if get_int @@ get_val bv > 0 then
          eval_ifelse @@ stmts if_blk
          (* eval_block_fn
            { ctx with pack_addr = ctx.free_addr }
            in_fn convt palcs @@ stmts if_blk
          >>= fun (c, ps) ->
          return ({ c with free_addr = c.pack_addr; pack_addr = old_pcka }, ps) *)
        else  
          eval_ifelse @@ stmts else_blk
          (* eval_block_fn
          { ctx with pack_addr = ctx.free_addr }
          in_fn convt palcs @@ stmts else_blk
          >>= fun (c, ps) -> return ({ c with free_addr = c.pack_addr; pack_addr = old_pcka }, ps) *)
        )
        >>= fun (ct, pals) -> return (ct, pals)
        (* let a = get_int @@ get_val bv in  *)
        (* print_string @@ "\n" ^ (Int.to_string @@ get_int @@ get_val bv) ^ "\n"; *)
        (* return (ctx, palcs) *)
    | T_ASSIGN (l, r) -> assign ctx l r in_fn convt palcs
    | _ -> error "stmt"

  and eval_expr (ctxs : exec_ctx) (in_fn : bool) convt (palcs : allocated) =
    function
    | VAR_NAME name -> (
        get_from_vars ctxs name >>= function
        | Some (_, _, v) -> return @@ ((ctxs, Vhval v), palcs)
        | None -> error @@ "Var undefined EXP" ^ name ^ Bool.to_string in_fn
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
    | ADD (e1, e2) -> op ctxs _add e1 e2 in_fn convt palcs
    | SUB (e1, e2) -> op ctxs _sub e1 e2 in_fn convt palcs
    | MUL (e1, e2) -> op ctxs _mul e1 e2 in_fn convt palcs
    | DIV (e1, e2) -> op ctxs _div e1 e2 in_fn convt palcs
    | MOD (e1, e2) -> op ctxs _mod e1 e2 in_fn convt palcs
    | AND (e1, e2) -> op ctxs _and e1 e2 in_fn convt palcs
    | OR (e1, e2) -> op ctxs _or e1 e2 in_fn convt palcs
    | EQUAL (e1, e2) -> op ctxs _eq e1 e2 in_fn convt palcs
    | NOT_EQUAL (e1, e2) -> op ctxs _neq e1 e2 in_fn convt palcs
    | GTE (e1, e2) -> op ctxs _gte e1 e2 in_fn convt palcs
    | GT (e1, e2) -> op ctxs _gt e1 e2 in_fn convt palcs
    | LTE (e1, e2) -> op ctxs _lte e1 e2 in_fn convt palcs
    | LT (e1, e2) -> op ctxs _lt e1 e2 in_fn convt palcs
    | NOT e ->
        eval_expr ctxs in_fn convt palcs e >>= fun ((cts, v), pls) ->
        _not v >>= fun v' -> return ((cts, v'), pls)
    | INDEXER (n, e) ->
        let xable ctxs name i =
          get_from_vars ctxs name >>= function
          | Some (CT_ARRAY (_, t), _, Vrval (_, Varraddress (_, addr)))
          | Some (CT_PTR t, _, Vrval (_, Vaddress (_, addr))) -> (
              sizeof ctxs t >>= fun s ->
              return @@ get_from_heap ctxs (addr + (i * s)) >>= function
              | Some v -> return @@ Vhval v
              | None -> return Vnull)
          | Some _ -> error "Not indexable"
          | None -> error "Var undefined"
        in
        eval_expr ctxs in_fn convt palcs e >>= fun ((cts, i), _) ->
        conv_to_int i >>= fun i' ->
        xable cts n @@ get_int i' >>= fun v' -> return ((cts, v'), palcs)
    | FUNC_CALL (n, vals) -> (
        match n with
        | "malloc" -> (
            match vals with
            | [ v ] -> (
                eval_expr ctxs in_fn convt palcs v >>= fun ((_, cnt), pal) ->
                match convt with
                | CT_PTR ctt -> malloc ctxs in_fn pal (get_int cnt) ctt
                | ttt -> error @@ "PPP" ^ " " ^ show_types ttt)
            | _ -> error "")
        | "main" -> main ctxs convt palcs
        | _ -> eval_fun { ctxs with last_value = Vnull } convt palcs n vals)
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
                        sizeof ctxs tt >>= fun x -> return @@ (x + ac) )
                | [] -> error "Nonexistent struct field"
              in
              pdng n args (return 0) >>= fun p ->
              match get_from_heap ctxs (bgn + p) with
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
            | INDEXER (n, e) ->
                eval_expr ctxs in_fn convt palcs e >>= fun ((_, i), pal) ->
                strct_padding tag n a @@ get_int i >>= fun v ->
                return ((ctxs, v), pal)
            | _ -> error "AC for INDEXERR")
        | (_, xx), _ -> error @@ "Unaccessorable" ^ show_v_value xx)
    | DEREFERENCE e -> (
        eval_expr ctxs in_fn convt palcs e >>= fun ((cs, v), pals) ->
        conv_to_int @@ get_val v >>= fun v' ->
        match get_from_heap cs (get_int @@ v') with
        | Some v'' -> return ((cs, Vhval v''), pals)
        | _ -> error "")
    | ADDRESS e -> (
        eval_expr ctxs in_fn convt palcs e >>= fun ((cs, v), pals) ->
        match v with
        | Vhval (Vrval (n, _)) -> (
            get_from_vars ctxs n >>= function
            | Some (_, a, _) ->
                return ((cs, Vint a), pals) (*TEST CONV INT TO ADDR *)
            | None -> error "")
        | _ -> error @@ "" ^ show_v_value @@ v
        (* conv_to_int @@ get_val v >>= fun v' -> _ *)
        (* match v' with  *))
    | TYPE t -> return @@ ((ctxs, Vtype t), palcs)

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
          let cur_ctx = new_ctx in
          match cur_ctx.jump_stmt with
          | None -> blk new_ctx in_fn pls' sts
          | Return _ | Break | Next -> return (new_ctx, pls'))
    in
    stmts >>= fun (_, _, vs) ->
    blk ctxs false palcs vs >>= fun (ctxs', pls) ->
    match ctxs'.jump_stmt with
    | Return _ -> return ((ctxs', ctxs'.last_value), pls)
    | _ -> error "Unexpected jump statement"

  and malloc ctxs (in_fn : bool) (palcs : allocated) size tt =
    let s' =
      sizeof ctxs tt >>= fun sot ->
      if size >= sot then return size else return sot
    in
    let adr = ctxs.free_addr in

    s' >>= fun s ->
    sizeof ctxs tt >>= fun sot ->
    cast_default_init0 ctxs @@ CT_ARRAY (s / sot, tt) >>= function
    | Vvalues vs ->
        List.fold_left
          (fun c v ->
            match v with
            | Vstructval (n, v') ->
                to_type v' >>= fun t ->
                c >>= fun c ->
                cast_default_dep_v c t n (CT_STRUCT "tag") >>= fun x -> return x
            | _ ->
                to_type v >>= fun t ->
                c >>= fun c ->
                cast_default_dep_v c t "" (CT_ARRAY (0, CT_INT)) >>= fun x ->
                return x)
          (return @@ ctxs) vs
        >>= fun x ->
        return @@ x >>= fun h ->
        (* print_string "\n"; *)
        (* print_string @@ dbg_print h; *)
        (* print_string @@ Int.to_string adr; *)
        (* print_string "\n";
           print_string @@ Int.to_string @@ adr + s; *)
        (* print_string "\n"; *)
        (* print_string h; *)
        (* List.iter (fun x ->print_string "\n";print_string @@ dbg_print x; print_string "\n") (h :: get_prev_tl ctxs'); *)
        return ((h, Vaddress (tt, adr)), (adr, adr + s - 1) :: palcs)
        (* return @@ ((h :: get_prev_tl ctxs, Vaddress adr), (adr, adr + s) :: palcs), (adr, adr + s) :: palcs) *)
    | _ -> error "MMM"

  and cast_default_dep_v ctxs t n format =
    let ctx = ctxs in
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
        | CT_INT | CT_CHAR | CT_VOID ->
            cast_default_init0 ctxs t >>= fun v ->
            add_in_heap ctx ctx.free_addr (Vdval (ctx.free_addr, v)) t
        | CT_PTR tt ->
            (* let rec get_ptr_t = function | CT_PTR tt -> get_ptr_t tt | tt -> tt in *)
            add_in_heap ctx ctx.free_addr
              (Vdval (ctx.free_addr, Vaddress (tt, 0)))
              t
            (* cast_default_init0 ctxs t >>= fun v -> *)
            (* create_ptr ctxs "." v @@ get_ptr_t t *)
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

  and eval_block_fn ctx in_fn convt palcs =
    let rec rm ctx i n =
      if i <= n then
        if not @@ b_srch i palcs then (
          (match get_from_heap ctx i with
          | Some (Vrval (n, _)) -> Hashtbl.remove ctx.vars n
          | _ -> ());
          Hashtbl.remove ctx.heap i;
          rm ctx (i + 1) n)
        else rm ctx (i + 1) n
      else ()
    in
    function
    | [] ->
        rm ctx ctx.pack_addr ctx.free_addr;
        return (ctx, palcs)
    | st :: sts -> (
        eval_stmt ctx in_fn convt palcs st >>= fun (new_ctx, pls) ->
        match new_ctx.jump_stmt with
        | None -> eval_block_fn new_ctx in_fn convt pls sts
        | Return _ | Break | Next ->
            rm ctx ctx.pack_addr ctx.free_addr;
            return
              ( {
                  new_ctx with
                  free_addr =
                    (match List.rev @@ List.sort compare palcs with
                    | _ :: p :: _ -> snd p + 1
                    | _ -> new_ctx.pack_addr);
                  jump_stmt = new_ctx.jump_stmt;
                  last_value = new_ctx.last_value;
                },
                pls ))

  (*
     allocated : allocated;
     vars : vars; !!!!
     heap : heap;
     struct_tags : struct_tags;
     functions : functions;
     free_addr : int;
     pack_addr : int;
     jump_stmt : jump_stmt;
     last_value : v_value;
  *)
  and eval_fun ctx convt palcs name vals =
    let ct = { ctx with vars = Hashtbl.create 16; last_value = Vnull } in
    (match get_from_functions ctx name with
    | Some f -> return f
    | None -> error "Function undeclared")
    >>= fun (_, args, vs) ->
    List.fold_left2
      (fun ct a v ->
        match a with
        | CARGS (_, n) ->
            ct >>= fun c ->
            eval_expr ctx false convt palcs v >>= fun ((_, v'), _) ->
            to_type v' >>= fun t -> create_var c n (Vhval (Vrval (n, v'))) t)
      (return ct) args vals
    >>= fun c ->
    eval_stmt c true convt palcs @@ T_BLOCK vs >>= fun (ctxs', pls) ->
    match ctxs'.jump_stmt with
    | Return _ ->
        return
          ( ( {
                ctx with
                free_addr = ctxs'.free_addr;
                last_value = ctxs'.last_value;
              },
              ctxs'.last_value ),
            pls )
    | _ -> error "Unexpected jump statement"

  and op (ctxs : exec_ctx) opp e1 e2 in_fn convt palcs =
    eval_expr ctxs in_fn convt palcs e1 >>= fun ((cs, v1), pls) ->
    eval_expr cs in_fn convt pls e2 >>= fun ((cts, v2), pls') ->
    opp (get_val @@ v1) (get_val @@ v2) >>= fun v' -> return ((cts, v'), pls')

  and cast_ks v1 v2 =
    match (v1, v2) with
    | Vaddress (tt, _), _ ->
        conv_to_addr tt v1 >>= fun v1' ->
        conv_to_addr tt v2 >>= fun v2' -> return @@ ((1, v1'), (4, v2'))
    | _, Vaddress (tt, _) ->
        conv_to_addr tt v1 >>= fun v1' ->
        conv_to_addr tt v2 >>= fun v2' -> return @@ ((4, v1'), (1, v2'))
    | _ ->
        conv_to_int v1 >>= fun v1' ->
        conv_to_int v2 >>= fun v2' -> return ((1, v1'), (1, v2'))

  and _add v1 v2 =
    cast_ks v1 v2 >>= fun ((k1, v1'), (k2, v2')) ->
    match (v1', v2') with
    | Vint v1'', Vint v2'' -> return @@ Vint (v1'' + v2'')
    | Vaddress (tt, v1''), Vaddress (_, v2'') ->
        return @@ Vaddress (tt, (k1 * v1'') + (k2 * v2''))
    | _ -> error "Invalid operands"

  and _sub v1 v2 =
    cast_ks v1 v2 >>= fun ((k1, v1'), (k2, v2')) ->
    match (v1', v2') with
    | Vint v1'', Vint v2'' -> return @@ Vint (v1'' - v2'')
    | Vaddress (tt, v1''), Vaddress (_, v2'') ->
        return @@ Vaddress (tt, (k1 * v1'') - (k2 * v2''))
    | _ -> error "Invalid operands"

  and _mul v1 v2 =
    cast_ks v1 v2 >>= fun ((k1, v1'), (k2, v2')) ->
    match (v1', v2') with
    | Vint v1'', Vint v2'' -> return @@ Vint (v1'' * v2'')
    | Vaddress (tt, v1''), Vaddress (_, v2'') ->
        return @@ Vaddress (tt, k1 * v1'' * k2 * v2'')
    | _ -> error "Invalid operands"

  and _div v1 v2 =
    cast_ks v1 v2 >>= fun ((k1, v1'), (k2, v2')) ->
    match (v1', v2') with
    | Vint v1'', Vint v2'' when v2'' <> 0 -> return @@ Vint (v1'' / v2'')
    | Vaddress (tt, v1''), Vaddress (_, v2'') when v2'' <> 0 ->
        return @@ Vaddress (tt, k1 * v1'' / (k2 * v2''))
    | _ -> error "Invalid operands"

  and _mod v1 v2 =
    cast_ks v1 v2 >>= fun ((k1, v1'), (k2, v2')) ->
    match (v1', v2') with
    | Vint v1'', Vint v2'' when v2'' <> 0 -> return @@ Vint (v1'' mod v2'')
    | Vaddress (tt, v1''), Vaddress (_, v2'') when v2'' <> 0 ->
        return @@ Vaddress (tt, k1 * v1'' mod (k2 * v2''))
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

  and to_type v =
    match get_val v with
    (* function *)
    | Vint _ -> return CT_INT
    | Vchar _ -> return CT_CHAR
    | Vaddress (tt, _) -> return @@ CT_PTR tt
    | Vstructval (_, v) -> to_type v
    | Vstaddress (tag, _) -> return @@ CT_STRUCT tag
    | Varraddress (tt, _) -> return @@ CT_ARRAY (0, tt)
    (* | Vhval rdv ->  *)
    (* | Vvalues _ -> CT_PTR CT_VOID *)
    | a -> error @@ "to_type" ^ show_v_value a

  and rewrite_var ctxs name t v addr =
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
    match t with
    | CT_INT | CT_CHAR ->
        Hashtbl.replace ctxs.vars name (t, addr, Vrval (name, v));
        Hashtbl.replace ctxs.heap addr (Vrval (name, v));
        return ctxs
    | CT_PTR tt ->
        conv_to_addr tt v >>= fun ad ->
        Hashtbl.replace ctxs.vars name (t, addr, Vrval (name, ad));
        Hashtbl.replace ctxs.heap addr (Vrval (name, ad));
        return ctxs
    | CT_ARRAY (l, t) -> (
        match v with
        | Vvalues _vs ->
            addr_fst >>= fun ad ->
            cast_default_init0 ctxs @@ CT_ARRAY (l, t) >>= fun dv ->
            return @@ lift_vvs _vs [] >>= fun vs ->
            (match dv with
            | Vvalues dvs ->
                return
                @@ List.map2
                     (fun v d ->
                       match (v, d) with
                       | Vnull, _ -> d
                       | Vvalues _, Vstructval (_, Vstaddress _) -> d
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
                        get_size t >>= fun inc -> return @@ (inc :: ac))
                  lifted_vs (return [])
                >>= fun incs ->
                List.fold_left2
                  (fun a _v _inc ->
                    a >>= fun a ->
                    (match get_from_heap ctxs a with
                    | Some (Vdval (_ad, vl)) -> return (_ad, vl)
                    | _ -> error "!!!")
                    >>= fun (_ad, ov) ->
                    match ov with
                    | Vstaddress _ | Varraddress _
                    | Vstructval (_, Vstaddress _)
                    | Vstructval (_, Varraddress _) ->
                        return @@ (a + _inc)
                    | _ ->
                        conv_v _v ov >>= fun v' ->
                        Hashtbl.replace ctxs.heap _ad (Vdval (_ad, v'));
                        return @@ (a + _inc))
                  (return ad) lifted_vs incs
            | _ -> error "XYN")
            >> return ctxs
        | Vaddress (_, a)
        | Varraddress (_, a)
        | Vstaddress (_, a)
        | Vstructval (_, Vaddress (_, a))
        | Vstructval (_, Varraddress (_, a))
        | Vstructval (_, Vstaddress (_, a)) ->
            Hashtbl.replace ctxs.vars name
              (CT_ARRAY (l, t), addr, Vrval (name, Varraddress (t, a)));
            Hashtbl.replace ctxs.heap addr (Vrval (name, Varraddress (t, a)));
            return @@ ctxs
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
                        Hashtbl.replace ctxs.heap a
                          (Vdval (_ad, Vstructval (nm, v')));
                        return @@ (a + inc))
                  (return ad) lifted_vs incs
            | _ -> error "CT_STRUCT__")
            >> return ctxs
        | Vaddress (_, a)
        | Varraddress (_, a)
        | Vstaddress (_, a)
        | Vstructval (_, Vaddress (_, a))
        | Vstructval (_, Varraddress (_, a))
        | Vstructval (_, Vstaddress (_, a)) ->
            Hashtbl.replace ctxs.vars name
              (t, addr, Vrval (name, Vstaddress (tag, a)));
            Hashtbl.replace ctxs.heap addr (Vrval (name, Vstaddress (tag, a)));
            return ctxs
        | _ -> error "Expected set of values")
    | _ -> error "1"

  and cast_default_struct_init (ctxs : exec_ctx) tag =
    let rec unpack_t (n : string) = function
      | CT_INT -> return [ (CT_INT, n) ]
      | CT_CHAR -> return [ (CT_CHAR, n) ]
      | CT_PTR t -> return [ (CT_PTR t, n) ]
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
              g >>= fun x -> return @@ ((CT_STRUCT tag, n) :: x)
          | None -> error "Struct undeclared" (* error "" *))
      | CT_VOID -> return [ (CT_VOID, n) ]
    in
    unpack_t tag @@ CT_STRUCT tag >>= function
    | (_t, _) :: tl ->
        List.fold_right
          (fun (t, n) ac ->
            ac >>= fun a ->
            cast_default_init t >>= fun dv -> return @@ (Vstructval (n, dv) :: a))
          tl (return [])
        >>= fun vsts ->
        cast_default_init _t >>= fun x -> return @@ (x :: vsts)
    | _ -> error "DEF STRUCT"

  and cast_default_init0 ctxs = function
    | CT_INT -> return @@ Vint 0
    | CT_CHAR -> return @@ Vchar 'n'
    | CT_STRUCT n ->
        cast_default_struct_init ctxs n >>= fun x -> return @@ Vvalues x
    | CT_PTR tt ->
        (* cast_default_ptr_init ctxs @@ CT_PTR tt >>= fun x -> return @@ Vvalues x *)
        return @@ Vaddress (tt, 0)
    | CT_ARRAY (size, tt) ->
        cast_default_arr_init ctxs size tt >>= fun x -> return @@ Vvalues x
    | CT_VOID -> error "void can't have values"

  and cast_default_arr_init (ctxs : exec_ctx) size tt =
    let to_list = function Vvalues vs -> vs | otherwise -> [ otherwise ] in
    let rec helper (acc : v_value list) s t =
      if s > 0 then
        cast_default_init0 ctxs t >>= fun xs ->
        helper (acc @ to_list xs) (s - 1) t
      else return acc
    in
    helper [] size tt

  and cast_default_ptr_init ctx t =
    let rec destruct acc = function
      | CT_PTR tt -> destruct (Vaddress (tt, -1) :: acc) tt
      | otherwise ->
          cast_default_init0 ctx otherwise >>= fun v ->
          return @@ List.rev @@ (v :: acc)
    in
    destruct [] t
  (* >>= fun vs -> return
     @@ List.map (fun x -> match x with | (Vaddress (CT_PTR tt, vv)) -> (Vaddress (tt, vv)) | otherwise -> otherwise) vs *)

  and assign (ctxs : exec_ctx) l_expr r_expr (in_fn : bool) convt palcs =
    eval_expr ctxs in_fn convt palcs l_expr >>= fun (p, _) ->
    match snd p with
    (* function *)
    | Vhval (Vrval (n, _)) ->
        let var =
          get_from_vars ctxs n >>= function
          | Some v -> return v
          | None -> error "var undefined?"
        in
        var >>= fun (t, addr, _) ->
        eval_expr ctxs in_fn t (* convt  *) palcs r_expr
        >>= fun ((ctxs', r), pls) ->
        return
        @@ {
             ctxs with
             last_value = ctxs'.last_value;
             free_addr = ctxs'.free_addr;
           }
        >>= fun cs ->
        conv_t (get_val r) t >>= fun r' ->
        rewrite_var cs n t r' addr >>= fun cs' -> return (cs', pls)
    | Vhval (Vdval (_ad, _v)) ->
        to_type _v >>= fun _convt ->
        eval_expr ctxs in_fn _convt palcs r_expr >>= fun ((ctxs', r), pls) ->
        return
        @@ {
             ctxs with
             last_value = ctxs'.last_value;
             free_addr = ctxs'.free_addr;
             jump_stmt = ctxs'.jump_stmt;
           }
        >>= fun cs ->
        conv_v (get_val r) _v >>= fun r' ->
        Hashtbl.replace cs.heap _ad (Vdval (_ad, get_val r'));
        return (cs, pls)
    | a -> error @@ show_v_value a

  and declare (ctxs : exec_ctx) name t (expr : expr option) in_fn convt palcs =
    let prfx = "." in
    (match t with
    | CT_INT | CT_CHAR -> (
        cast_default_init t >>= fun v ->
        create_var ctxs (prfx ^ name) (Vhval (Vrval (prfx ^ name, v))) t
        >>= fun h ->
        match expr with
        | None -> return @@ (h, palcs)
        | Some r -> assign h (VAR_NAME (prfx ^ name)) r in_fn t palcs)
    | CT_PTR tt -> (
        let rec get_ptr_t = function CT_PTR tt -> get_ptr_t tt | tt -> tt in
        cast_default_init0 ctxs t >>= fun v ->
        create_var ctxs (prfx ^ name) (Vhval (Vrval (prfx ^ name, v))) t
        >>= fun h ->
        match expr with
        | None -> return @@ (h, palcs)
        | Some r -> assign h (VAR_NAME (prfx ^ name)) r in_fn t palcs
        (* >>= fun v -> create_ptr ctxs (prfx ^ name) v @@ get_ptr_t tt
           >>= fun h ->
           match expr with
           | None | Some (LITERAL CNULL) -> return @@ (h, palcs)
           | Some r -> assign h (VAR_NAME (prfx ^ name)) r in_fn t palcs *)
        (*
                 let start_id = get_size @@ CT_PTR tt >>= fun inc -> return @@ ctxs.free_addr + inc in
                 cast_default_init t >>= fun v ->
                 create_var ctxs (prfx ^ name) (Vhval (Vrval (prfx ^ name, v))) t
                 >>= fun h ->
                 match expr with
                 | None | Some (LITERAL CNULL) ->
                     let rec pts ctx palcs t acc adr =
                       match t with
                       | CT_PTR tt -> (
                           pts ctx palcs tt acc (
                             adr >>= fun a -> sizeof ctx tt
                             >>= fun inc ->
                             match a with
                             | h :: _ -> return @@ h + inc :: a
                             | _ -> return @@ a)
                           >>= fun (((cs, v), pals), adrr) ->
                           malloc cs in_fn pals 1 tt >>= fun x -> return (x, adrr)

                           (* return _ *)
                         )
                           (* >>= fun (c, v), p) ->
                           match get_from_heap c with
                           | Some hv -> _
                           | None -> return (c, v), p) *)
                       | _ -> return (acc, adr)
                       (* match t with
                       | CT_PTR tt -> (
                           malloc ctx in_fn palcs 1 tt
                           >>= fun ((cs, v), pals)  -> pts cs pals tt @@ ((cs, v), pals) )
                       | _ -> return acc *)
                     in

                     (* malloc h in_fn palcs 1 tt >>= fun ((cs, v), pals) ->
                     conv_to_int v  *)

                     pts h palcs t ((h, Vnull), palcs) (return [h.free_addr])
                     >>= fun (((cs, v), pals), adrs) ->
                     adrs >>= fun adrs ->
                     (match adrs with
                       | _ :: tl ->
                       let rec helper ctx l id = match l with
                       | h ::tl -> (
                           match get_from_heap ctxs id with
                           | Some (Vdval (a', (Vaddress (tt, _)))) -> Hashtbl.replace ctxs.heap a' (Vdval (a', (Vaddress (tt, h)))); helper ctx tl (id + 4)
                           | _ -> helper ctx tl (id + 4)
                         )
                       | _ -> return ctx
                       in

                       start_id >>= fun sid -> helper ctxs tl (sid)
                       (* List.fold_left (
                         fun id a   ->
                           id >>= fun i -> (
                             match get_from_heap ctxs i with
                             | Some (Vdval (a', (Vaddress (tt, _)))) -> Hashtbl.replace ctxs.heap a' (Vdval (a', (Vaddress (tt, a)))); return @@ i + 4
                             | Some _ -> return @@ i + 4
                             | _ -> error ""
                             )
                           )  start_id ( tl) *)

                       | _ -> error ""  ) >>= fun _ ->
                     print_string "\n";
                     List.iter (fun x -> print_string @@ Int.to_string x; print_string "\n";) adrs;
                     print_string "\n";
                     conv_to_int v
                     >>= fun i ->
                     assign cs
                       (VAR_NAME (prfx ^ name))
                       (LITERAL (CINT (get_int i)))
                       in_fn t palcs
                 | Some r -> assign h (VAR_NAME (prfx ^ name)) r in_fn t palcs *)
        )
    | CT_ARRAY (_, t') -> (
        cast_default_init0 ctxs t >>= fun v ->
        create_arr ctxs (prfx ^ name) v t >>= fun h ->
        match expr with
        | None -> return @@ (h, palcs)
        | Some r -> assign h (VAR_NAME (prfx ^ name)) r in_fn t palcs
        (* cast_default_init0 ctxs t >>= fun v ->
           match expr with
           | None ->
               create_var ctxs (prfx ^ name)
                 (Vhval (Vrval (prfx ^ name, Varraddress (t', ctxs.free_addr))))
                 t
               >>= fun c ->
               return @@ c >>= fun cs' -> return (cs', palcs)
           | Some r ->
               create_arr ctxs (prfx ^ name) v t >>= fun h ->
               assign h (VAR_NAME name) r in_fn t palcs *))
    | CT_STRUCT tag -> (
        cast_default_init0 ctxs t >>= fun v ->
        create_struct ctxs (prfx ^ name) v t >>= fun h ->
        match expr with
        | None -> return @@ (h, palcs)
        | Some r -> assign h (VAR_NAME (prfx ^ name)) r in_fn t palcs)
    | CT_VOID | _ -> error "void haven't values")
    >>= fun (s_ctx, pls) ->
    let nahv =
      get_from_vars s_ctx (prfx ^ name) >>= function
      | Some v -> return v
      | None -> error "declare"
    in
    nahv >>= fun (t, a, hv) ->
    Hashtbl.add ctxs.vars name (t, a, Vrval (name, get_val @@ Vhval hv));
    Hashtbl.replace ctxs.heap a (Vrval (name, get_val @@ Vhval hv));
    Hashtbl.remove ctxs.vars (prfx ^ name);
    return (s_ctx, pls)

  and create_arr ctxs name vvs = function
    | CT_ARRAY (size, tt) -> (
        match vvs with
        | Vvalues vs ->
            let ctx = ctxs in
            let fst_val_addr =
              get_size @@ CT_ARRAY (size, tt) >>= fun s ->
              return @@ (ctx.free_addr + s)
            in
            fst_val_addr >>= fun ad ->
            create_var ctx name
              (Vhval (Vrval (name, Varraddress (tt, ad))))
              (CT_ARRAY (size, tt))
            >>= fun ctx ->
            let ctxs = ctx in
            List.fold_left
              (fun c v ->
                match v with
                | Vstructval (n, v') ->
                    to_type v' >>= fun t ->
                    c >>= fun c ->
                    cast_default_dep_v c t n (CT_STRUCT "tag") >>= fun x ->
                    return x
                | _ ->
                    to_type v >>= fun t ->
                    c >>= fun c ->
                    cast_default_dep_v c t "" (CT_ARRAY (0, CT_INT))
                    >>= fun x -> return x)
              (return @@ ctxs) vs
            >>= fun x -> return @@ x
        | _ -> error @@ "expected set of values" ^ show_v_value vvs)
    | _ -> error "not an array"

  and create_ptr ctx name vvs tt =
    (* function *)
    (* | CT_PTR tt -> ( *)
    match vvs with
    | Vvalues vs ->
        let hs, lv =
          match List.rev vs with
          | lv :: hs -> (List.rev hs, lv)
          | _ -> (vs, Vnull)
        in
        (match tt with
        | CT_INT | CT_CHAR ->
            let fst_addr = ctx.free_addr + 4 in
            let h, hs =
              match hs with h :: hs -> (h, hs) | [] -> (Vnull, hs)
            in
            to_type h >>= fun tt' ->
            let ttt =
              match tt' with CT_PTR tt -> tt | otherwise -> otherwise
            in
            create_var ctx name
              (Vhval (Vrval (name, Vaddress (ttt, ctx.free_addr + 4))))
              tt'
            (* add_in_heap ctx ctx.free_addr (Vrval (name, Vaddress (ttt, ctx.free_addr + 4))) tt' *)
            >>=
            fun ctx ->
            let _a =
              List.fold_left
                (fun _a v ->
                  _a >>= fun (ct, lv, acc) ->
                  to_type v >>= fun tt' ->
                  let ttt =
                    match tt' with CT_PTR tt -> tt | otherwise -> otherwise
                  in
                  add_in_heap ct ct.free_addr
                    (Vdval (ct.free_addr, Vaddress (ttt, lv + 4)))
                    tt'
                  >>= fun c -> return (c, lv + 4, (lv, lv + 4) :: acc))
                (return (ctx, fst_addr, []))
                hs
            in
            _a >>= fun (ct, lst, ps) ->
            (* List.iter (fun x -> print_string  "\n"; print_string @@ show_v_value x; print_string  "\n";) hs; *)

            (* List.iter (fun (x, y) -> print_string "\n"; print_string @@ Int.to_string x ^ " -> " ^  Int.to_string y; print_string "\n") @@ List.rev ps; *)
            add_in_heap ct ct.free_addr (Vdval (ct.free_addr, lv)) tt
            >>= fun c ->
            (* print_string @@ dbg_print c [] ^ "\n"; *)
            return c
            (* List.fold_left (fun acc) (return [fst_addr]) tl *)
            (* List.fold_left (
                 fun _a pt ->
                   _a >>= fun (a, ctx') -> to_type pt >>= fun tt' -> let ttt = match tt' with | CT_PTR tt -> tt | otherwise -> otherwise in
                   add_in_heap ctx' ctx'.free_addr (Vdval (ctx'.free_addr, Vaddress (ttt, a))) ttt
                   >>= fun c -> return @@ (a + 4, c) (*size ptr = 4 *)
                   )
               (return (fst_addr, ctx)) tl *)
            (* >> - ctx *)
            (* | CT_STRUCT tag ->
                let fst_addr = ctx.free_addr + 4 in
                cast_default_init0 ctx @@ CT_STRUCT tag >>= fun vvs ->
                create_struct ctx "." vvs @@ CT_STRUCT tag >>= fun ctx ->
                List.fold_left (
                  fun _a pt ->
                    _a >>= fun (a, ctx') -> to_type pt >>= fun tt' ->
                    add_in_heap ctx' ctx'.free_addr (Vdval (ctx'.free_addr, Vaddress (tt', a))) tt'
                    >>= fun c  -> sizeof ctx' tt >>= fun inc ->
                    return @@ (a + inc, c) (*size ptr = 4 *)
                    )
                (return (fst_addr, ctx)) tl *)
            (* >> return ctx *)
        | _ -> error "STRYCT ARR >>>> ")
        (* >>= fun (ad, x) -> to_type rv >>= fun t' ->  *)
        (* let ttt = match t' with | CT_PTR tt -> tt | otherwise -> otherwise in *)
        (* create_var x name (Vhval (Vrval (name, Vaddress (ttt, ad) ))) ttt *)
        >>=
        fun ctx -> return ctx
    | _ -> error @@ "expected set of valuesNEW" ^ show_v_value vvs

  (* ) *)
  (* | _ -> error "not a pointer" *)

  and create_struct ctxs name vvs = function
    | CT_STRUCT tag -> (
        let ctx = ctxs in
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
        match vvs with
        | Vvalues vs -> (
            match vs with
            | _ :: tl ->
                fst_val_addr >>= fun ad ->
                create_var ctxs name
                  (Vhval (Vrval (name, Vstaddress (tag, ad))))
                  (CT_STRUCT tag)
                >>= fun ctx ->
                let ctxs = ctx in
                List.fold_left
                  (fun c v ->
                    match v with
                    | Vstructval (n, v') ->
                        to_type v' >>= fun t ->
                        c >>= fun c ->
                        cast_default_dep_v c t n (CT_STRUCT tag) >>= fun x ->
                        return x
                    | _ -> error "XX")
                  (return ctxs) tl
                >>= fun x -> return x
            | _ -> return ctxs)
        | _ -> error @@ "expected set of values" ^ show_v_value vvs)
    | _ -> error "not a structure"

  and cast_default_init = function
    | CT_INT -> return @@ Vint 0
    | CT_CHAR -> return @@ Vchar 'n'
    | CT_STRUCT tag -> return @@ Vstaddress (tag, 0)
    | CT_PTR tt -> return @@ Vaddress (tt, 0)
    | CT_ARRAY (_, t) -> return @@ Varraddress (t, 0)
    | CT_VOID -> error "void can't have values"

  let test0 =
    declare_fun (() |> make_exec_ctx)
    @@ TOP_FUNC_DECL
         ( CT_INT,
           "f",
           [ CARGS (CT_INT, "a") ],
           T_BLOCK
             [
               RETURN
                 (VAR_NAME
                    "a"
                    (* LITERAL (CINT 10) *)
                    (* FUNC_CALL ("fn", []) *));
             ] )
    >>= fun ctx ->
    declare_fun ctx
    @@ TOP_FUNC_DECL
         ( CT_INT,
           "g",
           [],
           T_BLOCK
             [
               VAR_DECL ("a", CT_INT, Some (LITERAL (CINT 10)));
               VAR_DECL
                 ( "m",
                   CT_PTR CT_INT,
                   Some (FUNC_CALL ("malloc", [ LITERAL (CINT 1) ])) );
               (* VAR_DECL ("m", CT_PTR (CT_INT), Some (FUNC_CALL)); *)
               RETURN (FUNC_CALL ("f", [ LITERAL (CINT 11) ]));
             ] )
    >>= fun ctx ->
    declare_struct ctx
    @@ TOP_STRUCT_DECL
         ( "node",
           [
             CARGS (CT_INT, "value"); CARGS (CT_PTR (CT_STRUCT "node"), "next");
           ] )
    >>= fun ctx ->
    declare_struct ctx
    @@ TOP_STRUCT_DECL ("list", [ CARGS (CT_PTR (CT_STRUCT "node"), "head") ])
    >>= fun ctx ->
    declare_fun ctx
    @@ TOP_FUNC_DECL
         ( CT_INT,
           "addHead",
           [
             CARGS (CT_PTR (CT_STRUCT "list"), "list"); CARGS (CT_INT, "value");
           ],
           T_BLOCK
             [
               VAR_DECL
                 ( "nodee",
                   CT_PTR (CT_STRUCT "node"),
                   Some (FUNC_CALL ("malloc", [ LITERAL (CINT 1) ])) );
               T_ASSIGN
                 ( ACCESOR (DEREFERENCE (VAR_NAME "nodee"), VAR_NAME "value"),
                   VAR_NAME "value" );
               T_ASSIGN
                 ( ACCESOR (DEREFERENCE (VAR_NAME "nodee"), VAR_NAME "next"),
                   ACCESOR (DEREFERENCE (VAR_NAME "list"), VAR_NAME "head") );
               T_ASSIGN
                 ( ACCESOR (DEREFERENCE (VAR_NAME "list"), VAR_NAME "head"),
                   VAR_NAME "nodee" );
               RETURN (LITERAL (CINT 10) (* FUNC_CALL ("fn", []) *));
             ] )
    >>= fun ctx ->
    declare_fun ctx
    @@ TOP_FUNC_DECL
         ( CT_INT,
           "fff",
           [
             CARGS (CT_INT, "v");
           ],
           T_BLOCK
             [
              IF_ELSE (LT (VAR_NAME "v", LITERAL (CINT 3)), 
                T_BLOCK [
                  (* VAR_DECL ("m", CT_PTR (CT_INT), Some (FUNC_CALL ("malloc", [LITERAL (CINT 1)]))); *)
                  (* T_ASSIGN (DEREFERENCE (VAR_NAME "m"), VAR_NAME "v"); *)
                  (* EXPRESSION (FUNC_CALL ("fff", [(ADD (VAR_NAME "v", LITERAL (CINT 1)))] )); *)
                  T_ASSIGN (VAR_NAME "v", FUNC_CALL ("fff", [(ADD (VAR_NAME "v", LITERAL (CINT 1)))]));
                ],
                T_BLOCK []);
                RETURN (VAR_NAME "v");
             ] )
    >>= fun ctx ->
    declare_fun ctx
    @@ TOP_FUNC_DECL
         ( CT_INT,
           "main",
           [],
           T_BLOCK
             [
               (* VAR_DECL ("a", CT_INT, None); *)
               (* VAR_DECL ("aa", CT_PTR (CT_INT), Some (ADDRESS (VAR_NAME "a"))); *)

               (* VAR_DECL ("tst", CT_ARRAY (2, CT_STRUCT "node"), None); *)
               (* VAR_DECL ("tst0",  CT_STRUCT "node", Some (INDEXER ("tst", LITERAL (CINT 1)))); *)

               (* VAR_DECL
                    ( "ppt",
                      CT_PTR CT_INT,
                      Some
                        ((* LITERAL (CINT 100); *)
                           FUNC_CALL
                           ("malloc", [ LITERAL (CINT 8) ]) (* LITERAL (CNULL) *))
                    );
                  T_ASSIGN
                    ( DEREFERENCE (ADD (VAR_NAME "ppt", LITERAL (CINT 1))),
                      LITERAL (CINT 100) ); *)
               (* IF_ELSE
                 ( LT (LITERAL (CINT 1), LITERAL (CINT 2)),
                   T_BLOCK
                     [
                       VAR_DECL ("a", CT_INT, None); VAR_DECL ("b", CT_INT, None);
                     ],
                   T_BLOCK [] ); *)
                   EXPRESSION (FUNC_CALL ("fff", [LITERAL (CINT 0)]));
               RETURN
                 ((* FUNC_CALL ("f", [ LITERAL (CINT 11) ]) *)
                    LITERAL (CINT 0));
             ] )
    >>= fun ctx ->
    (* eval_stmt ctx false CT_INT [ (max_int, max_int) ]
       @@ VAR_DECL ("ptr",
       (* CT_ARRAY (1, CT_PTR (CT_INT)), *)
       CT_PTR (CT_PTR (CT_CHAR)),
       (* None *)
       Some (FUNC_CALL ("malloc", [LITERAL (CINT 8)]))
       ) *)

    (* cast_default_ptr_init ctx @@  CT_PTR (CT_PTR (CT_CHAR))
       >>= fun vvs -> create_ptr ctx "pointer" (Vvalues vvs) @@ CT_CHAR *)
    eval_stmt ctx false CT_INT [ (max_int, max_int) ]
    @@  EXPRESSION (FUNC_CALL ("fff", [LITERAL (CINT 0  )]));
    (* EXPRESSION (FUNC_CALL ("main", [])) *)
    >>= fun (c, als) -> return @@ dbg_print c als

  (* >>= fun x -> return @@ dbg_print x [] *)

  let rec collect ctx stmts =
    match stmts with
    | [] -> return ctx
    | top :: tops -> (
        match top with
        | TOP_FUNC_DECL _ ->
            declare_fun ctx top >>= fun ctx' -> collect ctx' tops
        | TOP_STRUCT_DECL _ ->
            declare_struct ctx top >>= fun ctx' -> collect ctx' tops
        | _ -> collect ctx tops (* eval' ctx palcs st *))

  let eval ctx stmts =
    collect ctx stmts >>= fun ct ->
    eval_stmt ct false CT_INT [ (max_int, max_int) ]
    @@ EXPRESSION (FUNC_CALL ("main", []))
    >>= fun (c, als) -> return @@ dbg_print c als
  (*
     print_string @@ Result.get_ok Interpreterctx.E.test0;;
  *)
end

module E = Eval (Result)

let eval ctx prg = E.eval ctx prg
