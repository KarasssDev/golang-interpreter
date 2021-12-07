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
  | Vnull
  | Vinitializer of expr list
  | Vvalues of v_value list
  | Vtype of types
  | Vfuncdec of string
  | Vstructdec of string
  | Vglob of int * v_value
[@@deriving show { with_path = false }]

type exec_ctx = {
  allocated : allocated;
  vars : vars;
  heap : heap;
  struct_tags : struct_tags;
  functions : functions;
  free_addr : int;
  pack_addr : int;
  jump_stmt : jump_stmt;
  last_value : v_value;
  have_ret : bool;
  strct_bgns : strct_bgns;
  cur_t : types;
}
[@@deriving show { with_path = false }]

and vars = (string, types * int * h_value) Ast.Hashtbl.t
[@@deriving show { with_path = false }]

and heap = (int, h_value) Ast.Hashtbl.t [@@deriving show { with_path = false }]

and functions =
  (string, vars * types * args list * statements list) Ast.Hashtbl.t
[@@deriving show { with_path = false }]

and struct_tags = (string, (types * string) list) Ast.Hashtbl.t
[@@deriving show { with_path = false }]

and jump_stmt = None | Break | Continue | Return of v_value
[@@deriving show { with_path = false }]

and allocated = (int * int) list [@@deriving show { with_path = false }]

and strct_bgns = (int, string) Ast.Hashtbl.t

let make_exec_ctx () =
  {
    allocated = [];
    vars = Ast.Hashtbl.create 16;
    heap = Ast.Hashtbl.create 16;
    struct_tags = Ast.Hashtbl.create 16;
    functions = Ast.Hashtbl.create 16;
    jump_stmt = None;
    last_value = Vvoid;
    free_addr = 0;
    pack_addr = 0;
    have_ret = false;
    strct_bgns = Ast.Hashtbl.create 16;
    cur_t = CT_VOID;
  }

let make_dep_ctx ctx () =
  {
    allocated = ctx.allocated;
    heap = ctx.heap;
    struct_tags = ctx.struct_tags;
    functions = ctx.functions;
    free_addr = ctx.free_addr;
    pack_addr = ctx.free_addr;
    vars = Ast.Hashtbl.create 16;
    jump_stmt = None;
    last_value = Vvoid;
    have_ret = false;
    strct_bgns = Ast.Hashtbl.create 16;
    cur_t = CT_VOID;
  }

let dbg_print ctx palcs =
  "\n*******************\n" ^ "\nstruct_tags: "
  ^ show_struct_tags ctx.struct_tags
  ^ "\nfunctions: "
  ^ show_functions ctx.functions
  ^ "\npack_addr: "
  ^ Int.to_string ctx.pack_addr
  ^ "\nfree_addr: "
  ^ Int.to_string ctx.free_addr
  ^ "\nret: "
  ^ Bool.to_string ctx.have_ret
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
    | CT_CHAR | CT_VOID -> return 1

  let pt_size = 4

  let get_from_heap ctx addr =
    match Ast.Hashtbl.find_opt ctx.heap addr with
    | Some v -> v
    | None ->
        Ast.Hashtbl.add ctx.heap addr @@ Vdval (0, Vint 0);
        Vdval (0, Vint 0)

  let get_from_vars ctx name emsg =
    match Ast.Hashtbl.find_opt ctx.vars name with
    | Some (t, a, Vrval (n, Vglob (aa, v))) -> (
        match get_from_heap ctx a with
        | Vrval (nn, vv) -> return (t, a, Vrval (nn, Vglob (aa, vv)))
        | _ -> error "Var undefined")
    | Some v -> return v
    | None -> error emsg

  let get_from_struct_tags ctx tag =
    get_from_vars ctx tag "Struct undefined" >>= fun _ ->
    return @@ Ast.Hashtbl.find_opt ctx.struct_tags tag

  let rec sizeof ctx t =
    match t with
    | CT_INT | CT_PTR _ | CT_CHAR _ | CT_VOID -> get_size t
    | CT_ARRAY (size, tt) -> sizeof ctx tt >>= fun x -> return @@ (x * size)
    | CT_STRUCT tag -> (
        get_from_struct_tags ctx tag >>= function
        | Some ps ->
            List.fold_left
              (fun acc (tt, _) ->
                acc >>= fun ac ->
                sizeof ctx tt >>= fun inc -> return @@ (ac + inc))
              (return 0) ps
            >>= fun x ->
            get_size @@ CT_STRUCT "tag" >>= fun inc -> return @@ (x + inc)
        | None -> error "struct undefined")

  let add_in_vars ctx name addr v t =
    match Hashtbl.find_opt ctx.vars name with
    | Some _ -> error @@ "name: " ^ name ^ " already using"
    | None ->
        Ast.Hashtbl.add ctx.vars name (t, addr, v);
        return ctx

  let add_in_heap ctx addr v t =
    let cur_addr = ctx.free_addr in
    let v' =
      match v with
      | Vrval (a, Vstaddress (b, _)) -> Vrval (a, Vstaddress (b, addr + pt_size))
      | Vdval (a, Vstaddress (b, _)) -> Vdval (a, Vstaddress (b, addr + pt_size))
      | otherwice -> otherwice
    in
    Ast.Hashtbl.add ctx.heap addr v';
    get_size t >>= fun size ->
    return @@ { ctx with free_addr = cur_addr + size }

  let create_var ctx name (v : v_value) t =
    match v with
    | Vhval (Vrval (_n, _v)) ->
        let ctx = ctx in
        add_in_vars ctx name ctx.free_addr (Vrval (_n, _v)) t >>= fun ctx ->
        add_in_heap ctx ctx.free_addr (Vrval (_n, _v)) t
    | _ -> error "create_var"

  let add_in_struct_tags ctx tag args =
    create_var ctx tag (Vhval (Vrval (tag, Vglob (0, Vstructdec tag)))) CT_VOID
    >>= fun ctx' ->
    Ast.Hashtbl.add ctx'.struct_tags tag args;
    return ctx'

  let add_in_functions ctx name (typ, args, sts) =
    let add_in_functions' ctx name (vrs, typ, args, sts) =
      create_var ctx name
        (Vhval (Vrval (name, Vglob (0, Vfuncdec name))))
        CT_VOID
      >>= fun ctx' ->
      Hashtbl.iter (fun k v -> Hashtbl.add vrs k v) ctx'.vars;
      Ast.Hashtbl.add ctx'.functions name (vrs, typ, args, sts);
      return ctx'
    in
    add_in_functions' ctx name (Hashtbl.create 16, typ, args, sts)

  let get_from_functions ctx name =
    get_from_vars ctx name "Function not in scope"
    >> return @@ Ast.Hashtbl.find_opt ctx.functions name

  let declare_struct ctx = function
    | TOP_STRUCT_DECL (name, args) ->
        let get_types (args : args list) =
          let get_pair (CARGS (t, n)) = (t, n) in
          List.fold_right (fun nt ts -> get_pair nt :: ts) args []
        in
        add_in_struct_tags ctx name (get_types args)
    | _ -> error "not a struct declaration"

  let declare_fun ctx = function
    | TOP_FUNC_DECL (ret_t, name, args, blk) -> (
        match blk with
        | BLOCK stmts -> (
            let rec is_correct_void stmts r =
              match stmts with
              | s :: st -> (
                  match s with
                  | RETURN ret_e -> (
                      match ret_e with
                      | LITERAL CVOID -> is_correct_void st (r && true)
                      | _ -> is_correct_void st (r && false))
                  | _ -> is_correct_void st r)
              | _ -> r
            in
            match ret_t with
            | CT_VOID when is_correct_void stmts true ->
                add_in_functions ctx name (ret_t, args, stmts)
            | CT_VOID -> error "Void function can't return nothing"
            | CT_INT | CT_CHAR | CT_STRUCT _ | CT_PTR _ ->
                add_in_functions ctx name (ret_t, args, stmts)
            | _ -> error "Undexpected type for function")
        | _ -> error "expected block")
    | _ -> return ctx

  let get_val = function
    | Vhval (Vrval (_, v)) | Vhval (Vdval (_, v)) -> v
    | v -> v

  let rec conv_to_addr ctx tt = function
    | Vstructval (_, Vint v) | Vint v -> return @@ Vaddress (tt, v)
    | Vstructval (_, Vchar v) | Vchar v -> return @@ Vaddress (tt, Char.code v)
    | Vstructval (_, Vaddress (_, v)) | Vaddress (_, v) ->
        return @@ Vaddress (tt, v)
    | Vnull -> return @@ Vaddress (tt, 0)
    | Varraddress (_, v) -> return @@ Vaddress (tt, v)
    | Vglob (aa, g) -> (
        match get_val @@ Vhval (get_from_heap ctx aa) with
        | Vglob (_, gv) -> conv_to_addr ctx tt gv
        | otherwise -> conv_to_addr ctx tt otherwise)
    | _ -> error @@ "Adress expected"

  let rec conv_to_int ctx v =
    match get_val v with
    | Vint v -> return @@ Vint v
    | Vchar v -> return @@ Vint (Char.code v)
    | Vaddress (_, v) -> return @@ Vint v
    | Varraddress (_, v) -> return @@ Vint v
    | Vnull -> return @@ Vint 0
    | Vstructval (_, v) -> conv_to_int ctx v
    | Vstaddress (_, v) -> return @@ Vint 0
    | Vglob (aa, g) -> (
        match get_val @@ Vhval (get_from_heap ctx aa) with
        | Vglob (_, gv) -> conv_to_int ctx gv
        | otherwise -> conv_to_int ctx otherwise)
    | _ -> error @@ "Integer expected "

  let rec conv_to_char ctx = function
    | Vint v | Vaddress (_, v) ->
        return @@ Vchar (String.get (Int.to_string v) 0)
    | Vchar v -> return @@ Vchar v
    | Vnull -> return @@ Vchar 'n'
    | Vstructval (_, v) -> conv_to_char ctx v
    | Vglob (aa, g) -> (
        match get_val @@ Vhval (get_from_heap ctx aa) with
        | Vglob (_, gv) -> conv_to_char ctx gv
        | otherwise -> conv_to_char ctx otherwise)
    | _ -> error "Char expected"

  let conv_t ctx v = function
    | CT_INT -> conv_to_int ctx v
    | CT_CHAR -> conv_to_char ctx v
    | CT_PTR tt -> conv_to_addr ctx tt v
    | CT_VOID -> error "Void doesn't contain value"
    | _ -> return v

  let rec to_type ctx v =
    match get_val v with
    | Vint _ -> return CT_INT
    | Vchar _ -> return CT_CHAR
    | Vaddress (tt, _) -> return @@ CT_PTR tt
    | Vstructval (_, v) -> to_type ctx v
    | Vstaddress (tag, _) -> return @@ CT_STRUCT tag
    | Varraddress (tt, _) -> return @@ CT_ARRAY (0, tt)
    | Vvalues (x :: _) -> (
        match x with
        | Vstaddress _ -> to_type ctx x
        | _ -> error @@ "Type conversion error ")
    | Vnull -> return CT_VOID
    | Vvoid -> return CT_VOID
    | Vglob (aa, g) -> (
        match get_val @@ Vhval (get_from_heap ctx aa) with
        | Vglob (_, gv) -> to_type ctx gv
        | otherwise -> to_type ctx otherwise)
    | _ -> error @@ "Type conversion error"

  let rec conv_v ctx v _v =
    match _v with
    | Vint _ -> conv_t ctx v CT_INT
    | Vchar _ -> conv_t ctx v CT_CHAR
    | Vaddress (tt, _) -> conv_t ctx v (CT_PTR tt)
    | Vstructval (n, v') ->
        conv_v ctx v v' >>= fun v'' -> return @@ Vstructval (n, v'')
    | Vnull -> to_type ctx v >>= fun t -> conv_t ctx v t
    | Vvoid -> error "Void doesn't contain value1 "
    | Vstaddress (tag, a) -> return @@ Vstaddress (tag, a)
    | _ -> error @@ "Unexpected expr "

  let get_int = function Vint v -> v | _ -> 0

  let is_true ctx cond =
    conv_to_int ctx @@ get_val cond >>= fun x -> return (get_int x > 0)

  let rec eval_stmt (ctx : exec_ctx) (from_main : bool) (in_fn : bool) rwrt
      (convt : types) (cur_t : types) (palcs : allocated) = function
    | VAR_DECL (name, t, expr) ->
        declare ctx name t expr from_main in_fn rwrt convt cur_t palcs
        >>= fun (ctx', pls) -> return (ctx', pls)
    | EXPRESSION (FUNC_CALL (n, vs)) ->
        eval_expr ctx from_main in_fn convt cur_t palcs @@ FUNC_CALL (n, vs)
        >>= fun ((ctxs', lv), pls) -> return (ctxs', pls)
    | EXPRESSION _ -> error "unexpected exoression"
    | RETURN e ->
        eval_expr ctx from_main in_fn convt cur_t palcs e
        >>= fun ((ctxs', v), pls) ->
        return
          {
            ctx with
            jump_stmt = Return (get_val v);
            last_value = v;
            free_addr = ctxs'.free_addr;
            have_ret = true;
          }
        >>= fun cs -> return (cs, pls)
    | BLOCK stmts -> eval_fn_blck ctx from_main in_fn convt cur_t palcs stmts
    | IF_ELSE (e, if_blk, else_blk) ->
        eval_expr ctx from_main in_fn convt cur_t palcs e
        >>= fun ((ct, bv), pals) ->
        let stmts blk = match blk with BLOCK stmts -> stmts | _ -> [] in
        let old_pcka = ctx.pack_addr in
        let eval_ifelse blk =
          eval_ifel_blck
            { ct with pack_addr = ctx.free_addr }
            from_main in_fn rwrt convt cur_t palcs blk
          >>= fun (c, ps) ->
          return ({ c with free_addr = c.pack_addr; pack_addr = old_pcka }, ps)
        in
        conv_to_int ct @@ get_val bv >>= fun x ->
        (if get_int x > 0 then eval_ifelse @@ stmts if_blk
        else
          match stmts else_blk with
          | [] -> return (ct, pals)
          | _ -> eval_ifelse @@ stmts else_blk)
        >>= fun (ct, pals) -> return (ct, pals)
    | IF (e, blk) ->
        eval_stmt ctx from_main in_fn rwrt convt cur_t palcs
        @@ IF_ELSE (e, blk, BLOCK [])
    | ASSIGN (l, r) -> assign ctx l r from_main in_fn convt cur_t palcs
    | WHILE (e, blk) -> eval_cycle ctx from_main in_fn convt cur_t palcs e blk
    | BREAK -> return ({ ctx with jump_stmt = Break }, palcs)
    | CONTINUE -> return ({ ctx with jump_stmt = Continue }, palcs)
    | ASSIGN_SUB (le, re) ->
        eval_stmt ctx from_main in_fn rwrt convt cur_t palcs
        @@ ASSIGN (le, SUB (le, re))
    | ASSIGN_ADD (le, re) ->
        eval_stmt ctx from_main in_fn rwrt convt cur_t palcs
        @@ ASSIGN (le, ADD (le, re))
    | ASSIGN_MUL (le, re) ->
        eval_stmt ctx from_main in_fn rwrt convt cur_t palcs
        @@ ASSIGN (le, MUL (le, re))
    | ASSIGN_DIV (le, re) ->
        eval_stmt ctx from_main in_fn rwrt convt cur_t palcs
        @@ ASSIGN (le, DIV (le, re))
    | ASSIGN_MOD (le, re) ->
        eval_stmt ctx from_main in_fn rwrt convt cur_t palcs
        @@ ASSIGN (le, MOD (le, re))
    | FOR (d, be, e, blk) ->
        let vars' : vars = Hashtbl.create 16 in
        Hashtbl.iter (fun n v -> Hashtbl.add vars' n v) ctx.vars;
        (match d with
        | Some dd ->
            eval_stmt { ctx with vars = vars' } from_main in_fn true convt cur_t
              palcs dd
        | None -> return (ctx, palcs))
        >>= fun (c, pals) ->
        (let get_stmts = function BLOCK st -> st | _ -> [] in
         match be with
         | Some bbe -> (
             match e with
             | Some ee ->
                 eval_stmt c from_main in_fn false convt cur_t pals
                 @@ WHILE (bbe, BLOCK (get_stmts blk @ [ ee ]))
             | None ->
                 eval_stmt c from_main in_fn false convt cur_t pals
                 @@ WHILE (bbe, blk))
         | None -> (
             match e with
             | Some ee ->
                 eval_stmt c from_main in_fn false convt cur_t pals
                 @@ WHILE (LITERAL (CINT 1), BLOCK (get_stmts blk @ [ ee ]))
             | None ->
                 eval_stmt c from_main in_fn false convt cur_t pals
                 @@ WHILE (LITERAL (CINT 1), blk)))
        >>= fun (c, als) ->
        Hashtbl.iter
          (fun n (t, a, hv) ->
            Hashtbl.replace ctx.vars n (t, a, get_from_heap c a))
          ctx.vars;
        return ({ ctx with free_addr = c.free_addr }, als)

  and eval_expr (ctxs : exec_ctx) from_main (in_fn : bool) convt cur_t
      (palcs : allocated) = function
    | VAR_NAME name ->
        get_from_vars ctxs name "Var undefined" >>= fun (t, _, v) ->
        return @@ (({ ctxs with cur_t = t }, Vhval v), palcs)
    | LITERAL CNULL -> return @@ ((ctxs, Vnull), palcs)
    | LITERAL (CINT v) -> return @@ ((ctxs, Vint v), palcs)
    | LITERAL (CCHAR c) -> return @@ ((ctxs, Vchar c), palcs)
    | LITERAL CVOID -> return @@ ((ctxs, Vvoid), palcs)
    | LITERAL (CARRAY ls) ->
        List.fold_right
          (fun e acc ->
            acc >>= fun vs ->
            eval_expr ctxs from_main in_fn convt cur_t palcs e
            >>= fun ((ctxs', v), _) -> return @@ (get_val v :: vs))
          ls (return [])
        >>= fun vs -> return @@ ((ctxs, Vvalues vs), palcs)
    | INITIALIZER es ->
        List.fold_right
          (fun e acc ->
            acc >>= fun vs ->
            eval_expr ctxs from_main in_fn convt cur_t palcs e
            >>= fun ((ctxs', v), _) -> return @@ (get_val v :: vs))
          es (return [])
        >>= fun vs -> return @@ ((ctxs, Vvalues vs), palcs)
    | ADD (e1, e2) -> op ctxs _add e1 e2 from_main in_fn convt cur_t palcs
    | SUB (e1, e2) -> op ctxs _sub e1 e2 from_main in_fn convt cur_t palcs
    | MUL (e1, e2) -> op ctxs _mul e1 e2 from_main in_fn convt cur_t palcs
    | DIV (e1, e2) -> op ctxs _div e1 e2 from_main in_fn convt cur_t palcs
    | MOD (e1, e2) -> op ctxs _mod e1 e2 from_main in_fn convt cur_t palcs
    | AND (e1, e2) -> op ctxs _and e1 e2 from_main in_fn convt cur_t palcs
    | OR (e1, e2) -> op ctxs _or e1 e2 from_main in_fn convt cur_t palcs
    | EQUAL (e1, e2) -> op ctxs _eq e1 e2 from_main in_fn convt cur_t palcs
    | NOT_EQUAL (e1, e2) -> op ctxs _neq e1 e2 from_main in_fn convt cur_t palcs
    | GTE (e1, e2) -> op ctxs _gte e1 e2 from_main in_fn convt cur_t palcs
    | GT (e1, e2) -> op ctxs _gt e1 e2 from_main in_fn convt cur_t palcs
    | LTE (e1, e2) -> op ctxs _lte e1 e2 from_main in_fn convt cur_t palcs
    | LT (e1, e2) -> op ctxs _lt e1 e2 from_main in_fn convt cur_t palcs
    | NOT e ->
        eval_expr ctxs from_main in_fn convt cur_t palcs e
        >>= fun ((cts, v), pls) ->
        _not cts v >>= fun v' -> return ((cts, v'), pls)
    | INDEXER (n, e) ->
        let xable ctxs name i =
          get_from_vars ctxs name "Var undefined" >>= function
          | CT_ARRAY (_, t), _, Vrval (_, Varraddress (_, addr))
          | CT_PTR t, _, Vrval (_, Vaddress (_, addr)) ->
              sizeof ctxs t >>= fun s ->
              return @@ (Vhval (get_from_heap ctxs (addr + (i * s))), cur_t)
          | _ -> error "Not indexable"
        in
        eval_expr ctxs from_main in_fn convt cur_t palcs e
        >>= fun ((cts, i), _) ->
        conv_to_int cts i >>= fun i' ->
        xable cts n @@ get_int i' >>= fun (v', cur_t) ->
        return (({ cts with cur_t }, v'), palcs)
    | FUNC_CALL (n, vals) -> (
        match n with
        | "malloc" -> (
            match vals with
            | [ v ] -> (
                eval_expr ctxs from_main in_fn convt cur_t palcs v
                >>= fun ((_, cnt), pal) ->
                match convt with
                | CT_PTR ctt -> malloc ctxs in_fn pal (get_int cnt) ctt
                | ttt -> malloc ctxs in_fn pal (get_int cnt) CT_INT)
            | _ -> error "")
        | "free" -> (
            match vals with
            | [ v ] -> free ctxs from_main in_fn convt cur_t palcs v
            | _ -> error "")
        | "sizeof" -> (
            match vals with
            | [ v ] -> sizeofn ctxs from_main in_fn convt cur_t palcs v
            | _ -> error "")
        | "main" -> main ctxs convt cur_t palcs
        | _ ->
            eval_fun
              { ctxs with last_value = Vvoid; pack_addr = ctxs.free_addr }
              from_main convt cur_t palcs n vals)
    | ACCESOR (e1, e2) -> (
        let strct_padding tag n bgn i =
          get_from_struct_tags ctxs tag >>= function
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
              | Vdval (_, Vstructval (_, Varraddress (t', a'))) ->
                  get_size t' >>= fun inc ->
                  return @@ Vhval (get_from_heap ctxs (a' + (i * inc)))
              | v -> return @@ Vhval v)
          | None -> error "Struct undefined"
        in
        let is_struct_pt_or_struct_e = function
          | CT_STRUCT _ -> true
          | _ -> false
        in
        eval_expr ctxs from_main in_fn convt cur_t palcs e1 >>= function
        | (c, Vhval (Vrval (_, Vstaddress (tag, a)))), pal
        | (c, Vhval (Vdval (_, Vstaddress (tag, a)))), pal
        | (c, Vstructval (_, Vstaddress (tag, a))), pal
          when is_struct_pt_or_struct_e c.cur_t -> (
            match e2 with
            | VAR_NAME n ->
                strct_padding tag n a 0 >>= fun v -> return ((ctxs, v), pal)
            | INDEXER (n, e) ->
                eval_expr ctxs from_main in_fn convt cur_t palcs e
                >>= fun ((_, i), pal) ->
                strct_padding tag n a @@ get_int i >>= fun v ->
                return ((ctxs, v), pal)
            | _ -> error "~~")
        | (_, _), _ -> error @@ "Unaccessorable")
    | DEREFERENCE e -> (
        eval_expr ctxs from_main in_fn convt cur_t palcs e
        >>= fun ((cs, v), pals) ->
        (match v with
        | Vhval (Vrval (_, Vaddress (CT_VOID, _)))
        | Vhval (Vdval (_, Vaddress (CT_VOID, _)))
        | Vhval (Vrval (_, Vglob (_, Vglob (_, Vaddress (CT_VOID, _))))) ->
            error "Void pointer dereference"
        | Vhval (Vrval (_, Vglob (aa, _))) -> (
            let addrr =
              match get_val @@ Vhval (get_from_heap cs aa) with
              | Vglob (_, gv) -> gv
              | otherwise -> otherwise
            in
            match addrr with
            | Vaddress (pt_t, _) | Varraddress (pt_t, _) -> return (pt_t, v)
            | _ -> error @@ "Can't be dereferenced")
        | Vhval (Vrval (_, Vaddress (pt_t, _)))
        | Vhval (Vdval (_, Vaddress (pt_t, _)))
        | Vhval (Vrval (_, Varraddress (pt_t, _)))
        | Vhval (Vdval (_, Varraddress (pt_t, _)))
        | Vhval (Vdval (_, Vstructval (_, Vaddress (pt_t, _))))
        | Vaddress (pt_t, _)
        | Varraddress (pt_t, _) ->
            return (pt_t, v)
        | _ -> error @@ "Can't be dereferenced")
        >>= fun (pt_t, v) ->
        conv_to_int cs @@ get_val v >>= fun v' ->
        match get_from_heap cs (get_int v') with
        | v'' when get_val @@ Vhval v'' <> Vnull ->
            return (({ cs with cur_t = pt_t }, Vhval v''), pals)
        | _ -> error @@ "Null pointer exception")
    | ADDRESS e -> (
        eval_expr ctxs from_main in_fn convt cur_t palcs e
        >>= fun ((cs, v), pals) ->
        match v with
        | Vhval (Vrval (n, _)) ->
            get_from_vars ctxs n "Var undefined" >>= fun (_, a, _) ->
            return ((cs, Vint a), pals)
        | _ -> error @@ "~~")
    | TYPE t -> return @@ ((ctxs, Vtype t), palcs)

  and sizeofn ctxs from_main in_fn convt cur_t palcs e =
    eval_expr ctxs from_main in_fn convt cur_t palcs e
    >>= fun ((ctx, v), als) ->
    match v with
    | Vtype t -> sizeof ctx t >>= fun s -> return ((ctx, Vint s), als)
    | _ -> error "sizof(): invalid type"

  and free ctxs from_main in_fn convt cur_t palcs e =
    eval_expr ctxs from_main in_fn convt cur_t palcs e
    >>= fun ((ctx, v), als) ->
    let glb = function
      | Vglob (aa, _) -> (
          match get_val @@ Vhval (get_from_heap ctx aa) with
          | Vglob (_, gv) -> gv
          | otherwise -> otherwise)
      | otherwise -> otherwise
    in
    match glb @@ get_val v with
    | (Vaddress (_, a) | Vstructval (_, Vaddress (_, a)))
      when b_srch a als && (not @@ List.mem_assoc a als) ->
        error "free(): invalid pointer"
    | Vaddress (_, a) | Vstructval (_, Vaddress (_, a)) ->
        (*was just ctx  *)
        let rmd_als = List.sort compare @@ List.remove_assoc a als in
        return
          ( ( {
                ctx with
                free_addr =
                  (match List.rev @@ List.sort compare rmd_als with
                  | _ :: p :: _ -> snd p + 1
                  | _ -> ctx.pack_addr);
              },
              v ),
            List.sort compare @@ List.remove_assoc a als )
    | _ -> error @@ "free(): invalid pointer"

  and repeat ctx from_main in_fn convt cur_t palcs body tmp_b cond =
    (* print_string @@ Int.to_string ctx.free_addr ^ "\n\n"; *)
    eval_expr ctx from_main in_fn convt cur_t palcs cond
    >>= fun ((c, cnd), pals) ->
    is_true c cnd >>= fun x ->
    if x then eval_cyc_body c from_main in_fn convt cur_t pals cond body tmp_b
    else return ({ c with free_addr = ctx.free_addr; last_value = Vnull }, pals)

  and eval_cyc_body ctx from_main in_fn convt cur_t palcs cond body tmp_b =
    match tmp_b with
    | [] -> repeat ctx from_main in_fn convt cur_t palcs body body cond
    | st :: sts -> (
        eval_stmt ctx from_main in_fn true convt cur_t palcs st
        >>= fun (ct, pls) ->
        match ct.jump_stmt with
        | Return _ -> return (ct, pls)
        | Break -> return ({ ct with last_value = Vnull }, pls)
        | Continue -> repeat ct from_main in_fn convt cur_t pls body body cond
        | None -> eval_cyc_body ct from_main in_fn convt cur_t pls cond body sts
        )

  and eval_cycle ctx from_main in_fn convt cur_t palcs cond = function
    | BLOCK stmts ->
        (let vars' : vars = Hashtbl.create 16 in
         Hashtbl.iter (fun n v -> Hashtbl.add vars' n v) ctx.vars;
         repeat { ctx with vars = vars' } from_main in_fn convt cur_t palcs
           stmts stmts cond)
        >>= fun (c, als) ->
        Hashtbl.iter
          (fun n (t, a, hv) ->
            Hashtbl.replace ctx.vars n (t, a, get_from_heap c a))
          ctx.vars;
        return ({ ctx with free_addr = c.free_addr }, als)
    | _ -> error "block expected "

  and main ctxs convt (cur_t : types) palcs =
    let stmts =
      get_from_functions ctxs "main" >>= function
      | Some f -> return f
      | None -> error "Function undeclared"
    in
    let rec blk ctxs (in_fn : bool) pls = function
      | [] -> return @@ (ctxs, pls)
      | st :: sts -> (
          eval_stmt ctxs true in_fn false convt cur_t pls st
          >>= fun (new_ctx, pls') ->
          let cur_ctx = new_ctx in
          match cur_ctx.jump_stmt with
          | None -> blk new_ctx in_fn pls' sts
          | Return _ | Break | Continue -> return (new_ctx, pls'))
    in
    let ctxs =
      {
        ctxs with
        vars = Hashtbl.create 16;
        last_value = Vvoid;
        have_ret = false;
      }
    in
    stmts >>= fun (vrrrrs, _, _, vs) ->
    Hashtbl.iter (fun k v -> Hashtbl.add ctxs.vars k v) vrrrrs;

    blk ctxs false palcs vs >>= fun (ctxs', pls) ->
    match ctxs'.jump_stmt with
    | Return _ -> return ((ctxs', ctxs'.last_value), pls)
    | _ -> error "main(): Unexpected jump statement"

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
                to_type ctxs v' >>= fun t ->
                c >>= fun c ->
                cast_default_dep_v c t n (CT_STRUCT "tag") >>= fun x -> return x
            | _ ->
                to_type ctxs v >>= fun t ->
                c >>= fun c ->
                cast_default_dep_v c t "" (CT_ARRAY (0, CT_INT)) >>= fun x ->
                return x)
          (return @@ ctxs) vs
        >>= fun x ->
        return @@ x >>= fun h ->
        return ((h, Vaddress (tt, adr)), (adr, adr + s - 1) :: palcs)
    (*  never come *)
    | _ -> return ((ctxs, Vvoid), palcs)

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
            add_in_heap ctx ctx.free_addr
              (Vdval (ctx.free_addr, Vaddress (tt, 0)))
              t
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

  and eval_fn_blck ctx from_main in_fn convt cur_t palcs =
    let rec rm ctx i n =
      if i <= n then
        if not @@ b_srch i palcs then (
          (match get_from_heap ctx i with
          | Vrval (n, _) -> Hashtbl.remove ctx.vars n
          | _ -> ());
          Hashtbl.remove ctx.heap i;
          rm ctx (i + 1) n)
        else rm ctx (i + 1) n
      else ()
    in
    function
    | [] ->
        rm ctx ctx.pack_addr ctx.free_addr;
        return
          ( {
              ctx with
              free_addr =
                (match List.rev @@ List.sort compare palcs with
                | _ :: p :: _ -> snd p + 1
                | _ -> ctx.pack_addr);
            },
            palcs )
    | st :: sts -> (
        eval_stmt ctx from_main in_fn false convt cur_t palcs st
        >>= fun (new_ctx, pls) ->
        match new_ctx.jump_stmt with
        | None -> eval_fn_blck new_ctx from_main in_fn convt cur_t pls sts
        | Return _ | Break | Continue ->
            get_ret_val new_ctx new_ctx.last_value >>= fun lv ->
            rm ctx ctx.pack_addr ctx.free_addr;
            return
              ( {
                  new_ctx with
                  free_addr =
                    (match List.rev @@ List.sort compare palcs with
                    | _ :: p :: _ -> snd p + 1
                    | _ -> new_ctx.pack_addr);
                  last_value = lv;
                },
                pls ))

  and eval_ifel_blck ctx from_main in_fn rwrt convt cur_t palcs =
    let rec rm ctx i n =
      if i <= n then
        if not @@ b_srch i palcs then (
          (match get_from_heap ctx i with
          | Vrval (n, _) -> Hashtbl.remove ctx.vars n
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
        eval_stmt ctx from_main in_fn rwrt convt cur_t palcs st
        >>= fun (new_ctx, pls) ->
        match new_ctx.jump_stmt with
        | None ->
            eval_ifel_blck new_ctx from_main in_fn rwrt convt cur_t pls sts
        | Return _ | Break | Continue ->
            rm ctx ctx.pack_addr ctx.free_addr;
            return
              ( {
                  new_ctx with
                  free_addr =
                    (match List.rev @@ List.sort compare palcs with
                    | _ :: p :: _ -> snd p + 1
                    | _ -> new_ctx.pack_addr);
                },
                pls ))

  and eval_fun ctx from_main convt cur_t palcs name vals =
    let ct = { ctx with vars = Hashtbl.create 16; last_value = Vvoid } in
    let is_void = function CT_VOID -> true | _ -> false in
    (get_from_functions ctx name >>= function
     | Some f -> return f
     | None -> error "Function undeclared")
    >>= fun (vrrrs, r_typ, args, vs) ->
    if List.length args = List.length vals then (
      Hashtbl.iter
        (fun k v ->
          match v with
          | _, _, Vrval (_, Vglob _) -> Hashtbl.add ct.vars k v
          | _ -> ())
        vrrrs;

      List.fold_left2
        (fun ct a v ->
          match a with
          | CARGS (_, n) ->
              ct >>= fun c ->
              eval_expr ctx from_main false convt cur_t palcs v
              >>= fun ((_, v'), _) ->
              to_type ctx @@ get_val v' >>= fun t ->
              create_var c n (Vhval (Vrval (n, get_val v'))) t)
        (return ct) args vals
      >>= fun c ->
      eval_stmt c false true true convt cur_t palcs @@ BLOCK vs
      >>= fun (ctxs', pls) ->
      get_ret_val ctxs' ctxs'.last_value >>= fun lv ->
      to_type ctx lv >>= fun x ->
      match ctxs'.jump_stmt with
      | Return _ ->
          return
            ( ( { ctx with free_addr = ctxs'.free_addr; last_value = lv },
                ctxs'.last_value ),
              pls )
      | _ when is_void r_typ ->
          return
            (({ ctx with free_addr = ctxs'.free_addr }, ctx.last_value), pls)
      | _ -> error "Unexpected jump statement")
    else error "Wrong number of arguments"

  and op (ctxs : exec_ctx) opp e1 e2 from_main in_fn convt cur_t palcs =
    eval_expr ctxs from_main in_fn convt cur_t palcs e1
    >>= fun ((cs, v1), pls) ->
    eval_expr cs from_main in_fn convt cur_t pls e2 >>= fun ((cts, v2), pls') ->
    opp ctxs (get_val @@ v1) (get_val @@ v2) >>= fun v' ->
    return ((cts, v'), pls')

  and cast_ks ctx v1 v2 =
    match (v1, v2) with
    | Vaddress (tt, _), _ | Varraddress (tt, _), _ ->
        conv_to_addr ctx tt v1 >>= fun v1' ->
        conv_to_addr ctx tt v2 >>= fun v2' ->
        sizeof ctx tt >>= fun k -> return @@ ((1, v1'), (k, v2'))
    | _, Vaddress (tt, _) | _, Varraddress (tt, _) ->
        conv_to_addr ctx tt v1 >>= fun v1' ->
        conv_to_addr ctx tt v2 >>= fun v2' ->
        sizeof ctx tt >>= fun k -> return @@ ((k, v1'), (1, v2'))
    | _ ->
        conv_to_int ctx v1 >>= fun v1' ->
        conv_to_int ctx v2 >>= fun v2' -> return ((1, v1'), (1, v2'))

  and _add ctx v1 v2 =
    cast_ks ctx v1 v2 >>= fun ((k1, v1'), (k2, v2')) ->
    match (v1', v2') with
    | Vint v1'', Vint v2'' -> return @@ Vint (v1'' + v2'')
    | Vaddress (tt, v1''), Vaddress (_, v2'') ->
        return @@ Vaddress (tt, (k1 * v1'') + (k2 * v2''))
    | _ -> error "Invalid operands"

  and _sub ctx v1 v2 =
    cast_ks ctx v1 v2 >>= fun ((k1, v1'), (k2, v2')) ->
    match (v1', v2') with
    | Vint v1'', Vint v2'' -> return @@ Vint (v1'' - v2'')
    | Vaddress (tt, v1''), Vaddress (_, v2'') ->
        return @@ Vaddress (tt, (k1 * v1'') - (k2 * v2''))
    | _ -> error "Invalid operands"

  and _mul ctx v1 v2 =
    cast_ks ctx v1 v2 >>= fun ((k1, v1'), (k2, v2')) ->
    match (v1', v2') with
    | Vint v1'', Vint v2'' -> return @@ Vint (v1'' * v2'')
    | Vaddress (tt, v1''), Vaddress (_, v2'') ->
        return @@ Vaddress (tt, k1 * v1'' * k2 * v2'')
    | _ -> error "Invalid operands"

  and _div ctx v1 v2 =
    cast_ks ctx v1 v2 >>= fun ((k1, v1'), (k2, v2')) ->
    match (v1', v2') with
    | Vint v1'', Vint v2'' when v2'' <> 0 -> return @@ Vint (v1'' / v2'')
    | Vaddress (tt, v1''), Vaddress (_, v2'') when v2'' <> 0 ->
        return @@ Vaddress (tt, k1 * v1'' / (k2 * v2''))
    | _ -> error "Invalid operands"

  and _mod ctx v1 v2 =
    cast_ks ctx v1 v2 >>= fun ((k1, v1'), (k2, v2')) ->
    match (v1', v2') with
    | Vint v1'', Vint v2'' when v2'' <> 0 -> return @@ Vint (v1'' mod v2'')
    | Vaddress (tt, v1''), Vaddress (_, v2'') when v2'' <> 0 ->
        return @@ Vaddress (tt, k1 * v1'' mod (k2 * v2''))
    | _ -> error "Invalid operands"

  and bool_to_num e = if e then 1 else 0

  and _and ctx v1 v2 =
    let vv1 = conv_to_int ctx v1 in
    let vv2 = conv_to_int ctx v2 in
    vv1 >>= fun n1 ->
    vv2 >>= fun n2 ->
    match (n1, n2) with
    | Vint o1, Vint o2 -> return @@ Vint (bool_to_num (o1 > 0 && o2 > 0))
    | _ -> error "Invalid operands"

  and _or ctx v1 v2 =
    let vv1 = conv_to_int ctx v1 in
    let vv2 = conv_to_int ctx v2 in
    vv1 >>= fun n1 ->
    vv2 >>= fun n2 ->
    match (n1, n2) with
    | Vint o1, Vint o2 -> return @@ Vint (bool_to_num (o1 > 0 || o2 > 0))
    | _ -> error "Invalid operands"

  and _lt ctx v1 v2 =
    let vv1 = conv_to_int ctx v1 in
    let vv2 = conv_to_int ctx v2 in
    vv1 >>= fun n1 ->
    vv2 >>= fun n2 ->
    match (n1, n2) with
    | Vint o1, Vint o2 -> return @@ Vint (bool_to_num (o1 < o2))
    | _ -> error "Invalid operands"

  and _gt ctx v1 v2 =
    let vv1 = conv_to_int ctx v1 in
    let vv2 = conv_to_int ctx v2 in
    vv1 >>= fun n1 ->
    vv2 >>= fun n2 ->
    match (n1, n2) with
    | Vint o1, Vint o2 -> return @@ Vint (bool_to_num (o1 > o2))
    | _ -> error "Invalid operands"

  and _lte ctx v1 v2 =
    let vv1 = conv_to_int ctx v1 in
    let vv2 = conv_to_int ctx v2 in
    vv1 >>= fun n1 ->
    vv2 >>= fun n2 ->
    match (n1, n2) with
    | Vint o1, Vint o2 -> return @@ Vint (bool_to_num (o1 <= o2))
    | _ -> error "Invalid operands"

  and _gte ctx v1 v2 =
    let vv1 = conv_to_int ctx v1 in
    let vv2 = conv_to_int ctx v2 in
    vv1 >>= fun n1 ->
    vv2 >>= fun n2 ->
    match (n1, n2) with
    | Vint o1, Vint o2 -> return @@ Vint (bool_to_num (o1 >= o2))
    | _ -> error "Invalid operands"

  and _not ctx v =
    let vv1 = conv_to_int ctx v in
    vv1 >>= fun n ->
    match n with
    | Vint o1 -> return @@ Vint (if not (o1 > 0) then 1 else 0)
    | _ -> error "Invalid operands"

  and _eq ctx v1 v2 =
    let vv1 = conv_to_int ctx v1 in
    let vv2 = conv_to_int ctx v2 in
    vv1 >>= fun n1 ->
    vv2 >>= fun n2 ->
    match (n1, n2) with
    | Vint o1, Vint o2 -> return @@ Vint (bool_to_num (o1 == o2))
    | _ -> error "Invalid operands"

  and _neq ctx v1 v2 =
    let vv1 = conv_to_int ctx v1 in
    let vv2 = conv_to_int ctx v2 in
    vv1 >>= fun n1 ->
    vv2 >>= fun n2 ->
    match (n1, n2) with
    | Vint o1, Vint o2 -> return @@ Vint (bool_to_num (o1 == o2))
    | _ -> error "Invalid operands"

  and rewrite_var ctxs name t v addr =
    let addr_fst =
      match get_from_heap ctxs addr with
      | Vrval (_, Vaddress (_, ad)) -> return ad
      | Vrval (_, Vstaddress (_, ad)) -> return ad
      | Vrval (_, Varraddress (_, ad)) -> return ad
      | Vdval (_, Vaddress (_, ad)) -> return ad
      | Vdval (_, Vstaddress (_, ad)) -> return ad
      | Vdval (_, Varraddress (_, ad)) -> return ad
      | _ -> error @@ "Var undefined"
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
        conv_to_addr ctxs tt v >>= fun ad ->
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
            | Vvalues dvs when List.length vs = List.length dvs ->
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
                        to_type ctxs v' >>= fun t ->
                        get_size t >>= fun inc -> return @@ (inc :: ac)
                    | otherwise ->
                        acc >>= fun ac ->
                        to_type ctxs otherwise >>= fun t ->
                        get_size t >>= fun inc -> return @@ (inc :: ac))
                  lifted_vs (return [])
                >>= fun incs ->
                if List.length incs = List.length lifted_vs then
                  List.fold_left2
                    (fun a _v _inc ->
                      a >>= fun a ->
                      (match get_from_heap ctxs a with
                      | Vdval (_ad, vl) -> return (_ad, vl)
                      | _ -> error "~~")
                      >>= fun (_ad, ov) ->
                      match ov with
                      | Vstaddress _ | Varraddress _
                      | Vstructval (_, Vstaddress _)
                      | Vstructval (_, Varraddress _) ->
                          return @@ (a + _inc)
                      | _ ->
                          conv_v ctxs _v ov >>= fun v' ->
                          Hashtbl.replace ctxs.heap _ad (Vdval (_ad, v'));
                          return @@ (a + _inc))
                    (return ad) lifted_vs incs
                else error "Wrong number of elements"
            | _ -> error "~~")
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
        | _ -> error @@ "Expected set of values")
    | CT_STRUCT tag -> (
        addr_fst >>= fun ad ->
        let v_cst =
          match v with
          | Vvalues (Vstaddress (tag', a') :: _) -> v
          | Vvalues vs -> Vvalues (Vstaddress (tag, 0) :: vs)
          | otherwise -> otherwise
        in
        match v_cst with
        | Vvalues (Vstaddress (tag', a') :: _vs) ->
            cast_default_init0 ctxs @@ CT_STRUCT tag >>= fun dv ->
            return @@ lift_vvs _vs [] >>= fun vs ->
            (match dv with
            | Vvalues (Vstaddress (_, _) :: dvs)
              when tag = tag' && List.length vs = List.length dvs ->
                return
                @@ List.map2
                     (fun v d ->
                       match (v, d) with
                       | Vvalues _, Vstructval (_, Vstaddress _) -> d
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
                        to_type ctxs v' >>= fun t -> return @@ (get_size t :: ac)
                    | _ -> acc)
                  lifted_vs (return [])
                >>= fun incs ->
                if List.length incs = List.length lifted_vs then
                  List.fold_left2
                    (fun a _v _inc ->
                      _inc >>= fun inc ->
                      a >>= fun a ->
                      (match get_from_heap ctxs a with
                      | Vdval (_ad, Vstructval (nm, vl)) -> return (_ad, nm, vl)
                      | _ -> return (0, "", Vint 0))
                      >>= fun (_ad, nm, ov) ->
                      match ov with
                      | Vstaddress _ | Varraddress _ -> return @@ (a + inc)
                      | _ ->
                          conv_v ctxs _v ov >>= fun v' ->
                          Hashtbl.replace ctxs.heap a
                            (Vdval (_ad, Vstructval (nm, v')));
                          return @@ (a + inc))
                    (return ad) lifted_vs incs
                else error "Wrong number of elements"
            | Vvalues (Vstaddress (_, _) :: dvs)
              when List.length vs = List.length dvs ->
                error "Wrong number of elements"
            | _ -> error "Type error")
            >> return ctxs
        | e -> error @@ show_v_value e ^ "  ----\n")
    | _ -> error "______1"

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
          get_from_struct_tags ctxs tag >>= function
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
          | None -> error "Struct undeclared")
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
    | _ -> error "~~"

  and cast_default_init0 ctxs = function
    | CT_INT -> return @@ Vint 0
    | CT_CHAR -> return @@ Vchar 'n'
    | CT_STRUCT n ->
        cast_default_struct_init ctxs n >>= fun x -> return @@ Vvalues x
    | CT_PTR tt -> return @@ Vaddress (tt, 0)
    | CT_ARRAY (size, tt) ->
        cast_default_arr_init ctxs size tt >>= fun x -> return @@ Vvalues x
    | CT_VOID -> return Vnull

  and get_ret_val ctx x =
    match get_val x with
    | Vstaddress (tag, a) -> (
        cast_default_init0 ctx @@ CT_STRUCT tag >>= function
        | Vvalues (_ :: vs) ->
            List.fold_right
              (fun v ac ->
                ac >>= fun ac ->
                to_type ctx v >>= fun t -> return @@ (t :: ac))
              vs
            @@ return []
            >>= fun ts ->
            List.fold_right
              (fun t ac ->
                ac >>= fun ac' ->
                get_size t >>= fun inc -> return @@ (inc :: ac'))
              ts (return [])
            >>= fun incs ->
            List.fold_left
              (fun p inc ->
                p >>= fun (a', ac) ->
                return
                @@ (a' + inc, (get_val @@ Vhval (get_from_heap ctx a')) :: ac))
              (return (a, []))
              incs
            >>= fun (_, init) ->
            return @@ Vvalues (Vstaddress (tag, a) :: List.rev init)
        | otherwise -> return otherwise)
    | otherwise -> return otherwise

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

  and assign (ctxs : exec_ctx) l_expr r_expr from_main (in_fn : bool) convt
      cur_t palcs =
    let rec get_ptr_t = function CT_PTR tt -> tt | _ -> CT_VOID in
    eval_expr ctxs from_main in_fn convt cur_t palcs l_expr >>= fun (p, _) ->
    match snd p with
    (* function *)
    | Vhval (Vrval (n, _)) -> (
        let var = get_from_vars ctxs n "Var undefined" >>= fun v -> return v in
        var >>= fun (t, addr, _) ->
        eval_expr ctxs from_main in_fn t cur_t palcs r_expr
        >>= fun ((ctxs', r), pls) ->
        get_ret_val ctxs' ctxs'.last_value >>= fun lv ->
        return
        @@ {
             ctxs with
             last_value = lv;
             free_addr = ctxs'.free_addr;
             pack_addr = ctxs'.pack_addr;
           }
        >>= fun cs ->
        conv_t cs (get_val r) t >>= fun r' ->
        rewrite_var cs n t r' addr >>= fun cs' ->
        match get_ptr_t t with
        | CT_STRUCT tag -> (
            get_from_vars cs' n "Var undefined" >>= function
            | _, _, Vrval (_, Vaddress (_, a)) -> (
                match get_from_heap cs' a with
                | Vdval (_, Vstaddress _) -> return (cs', pls)
                | Vdval (aa, vv) when get_val vv <> Vnull ->
                    (get_from_vars cs' n "Var undefined" >>= function
                     | _, a, _ ->
                         Hashtbl.remove cs'.heap a;
                         return ())
                    >>= fun _ ->
                    Hashtbl.replace cs'.heap aa
                      (Vdval (aa, Vstaddress (tag, aa + 4)));
                    return (cs', pls)
                | _ -> return (cs', pls))
            | _ -> return (cs', pls))
        | _ -> return (cs', pls))
    | Vhval (Vdval (_ad, _v)) ->
        to_type ctxs _v >>= fun _convt ->
        eval_expr ctxs from_main in_fn _convt cur_t palcs r_expr
        >>= fun ((ctxs', r), pls) ->
        get_ret_val ctxs' ctxs'.last_value >>= fun lv ->
        return
        @@ {
             ctxs with
             last_value = lv;
             free_addr = ctxs'.free_addr;
             pack_addr = ctxs'.pack_addr;
           }
        >>= fun cs ->
        (match _convt with
        | CT_STRUCT _ | CT_ARRAY _ ->
            rewrite_var cs "." _convt r _ad >>= fun cs ->
            ( get_from_vars cs "." "Var undefined" >>= fun (_, addr, _) ->
              Hashtbl.remove cs.heap addr;
              return () )
            >>= fun _ ->
            Hashtbl.remove cs.vars ".";
            return ()
        | _ ->
            conv_v cs (get_val r) _v >>= fun r' ->
            Hashtbl.replace cs.heap _ad (Vdval (_ad, get_val r'));
            return ())
        >> return (cs, pls)
    | _ -> error "~~"

  and declare (ctxs : exec_ctx) name t (expr : expr option) from_main in_fn rwrt
      convt cur_t palcs =
    let prfx = "." in

    (match Hashtbl.find_opt ctxs.vars name with
    | Some (t, a, Vrval (n, Vglob (_, v))) ->
        Hashtbl.remove ctxs.vars n;
        return ctxs
    | Some v when rwrt ->
        Hashtbl.remove ctxs.vars name;
        return ctxs
    | Some v -> error @@ "name " ^ name ^ "already using "
    | None -> return ctxs)
    >>= fun ctxs ->
    (match t with
    | CT_INT | CT_CHAR -> (
        cast_default_init t >>= fun v ->
        create_var ctxs (prfx ^ name) (Vhval (Vrval (prfx ^ name, v))) t
        >>= fun h ->
        match expr with
        | None -> return @@ (h, palcs)
        | Some r ->
            assign h (VAR_NAME (prfx ^ name)) r from_main in_fn t cur_t palcs)
    | CT_PTR tt -> (
        let rec get_ptr_t = function CT_PTR tt -> tt | _ -> CT_VOID in
        cast_default_init0 ctxs t >>= fun v ->
        create_var ctxs (prfx ^ name) (Vhval (Vrval (prfx ^ name, v))) t
        >>= fun h ->
        match expr with
        | None -> return @@ (h, palcs)
        | Some r ->
            assign h (VAR_NAME (prfx ^ name)) r from_main in_fn t cur_t palcs)
    | CT_ARRAY (_, t') -> (
        cast_default_init0 ctxs t >>= fun v ->
        create_arr ctxs (prfx ^ name) v t >>= fun h ->
        match expr with
        | None -> return @@ (h, palcs)
        | Some r ->
            assign h (VAR_NAME (prfx ^ name)) r from_main in_fn t cur_t palcs)
    | CT_STRUCT _ -> (
        cast_default_init0 ctxs t >>= fun v ->
        create_struct ctxs (prfx ^ name) v t >>= fun h ->
        match expr with
        | None -> return @@ (h, palcs)
        | Some r ->
            assign h (VAR_NAME (prfx ^ name)) r from_main in_fn t cur_t palcs)
    | CT_VOID | _ -> error "void haven't values")
    >>= fun (s_ctx, pls) ->
    let nahv =
      get_from_vars s_ctx (prfx ^ name) "Var undefined" >>= fun v -> return v
    in
    nahv >>= fun (t, a, hv) ->
    Hashtbl.add ctxs.vars name (t, a, Vrval (name, get_val @@ Vhval hv));
    Hashtbl.replace ctxs.heap a (Vrval (name, get_val @@ Vhval hv));
    Hashtbl.remove ctxs.vars (prfx ^ name);
    return (s_ctx, pls)

  and declare_top ctx = function
    | TOP_VAR_DECL (name, t, expr) -> (
        declare ctx name t expr false false false CT_VOID CT_VOID []
        >>= fun (ctx', _) ->
        get_from_vars ctx name "Var undefined" >>= function
        | t, a, Vrval (n, v) ->
            Hashtbl.replace ctx'.vars name (t, a, Vrval (n, Vglob (a, v)));
            Hashtbl.replace ctx'.heap a (Vrval (n, Vglob (a, v)));

            return ctx'
        | _ -> error "~~" (* return ctx' *))
    | _ -> return ctx

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
                    to_type ctxs v' >>= fun t ->
                    c >>= fun c ->
                    cast_default_dep_v c t n (CT_STRUCT "tag") >>= fun x ->
                    return x
                | _ ->
                    to_type ctxs v >>= fun t ->
                    c >>= fun c ->
                    cast_default_dep_v c t "" (CT_ARRAY (0, CT_INT))
                    >>= fun x -> return x)
              (return @@ ctxs) vs
            >>= fun x -> return @@ x
        | _ -> error @@ "expected set of values")
    | _ -> error "not an array"

  and create_struct ctxs name vvs = function
    | CT_STRUCT tag -> (
        let ctx = ctxs in
        let tps =
          get_from_struct_tags ctxs tag >>= function
          | Some v -> return v
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
                        to_type ctxs v' >>= fun t ->
                        c >>= fun c ->
                        cast_default_dep_v c t n (CT_STRUCT tag) >>= fun x ->
                        return x
                    | _ -> error "~~")
                  (return ctxs) tl
                >>= fun x -> return x
            | _ -> return ctxs)
        | _ -> error @@ "expected set of values")
    | _ -> error "not a structure"

  and cast_default_init = function
    | CT_INT -> return @@ Vint 0
    | CT_CHAR -> return @@ Vchar 'n'
    | CT_STRUCT tag -> return @@ Vstaddress (tag, 0)
    | CT_PTR tt -> return @@ Vaddress (tt, 0)
    | CT_ARRAY (_, t) -> return @@ Varraddress (t, 0)
    | CT_VOID -> error "void can't have values"

  let add_null ctx =
    add_in_heap ctx ctx.free_addr (Vdval (ctx.free_addr, Vnull)) CT_INT

  let test1 =
    add_null (() |> make_exec_ctx) >>= fun ctx ->
    declare_fun ctx
    @@ TOP_FUNC_DECL
         ( CT_VOID,
           "f",
           [],
           BLOCK
             [
               VAR_DECL
                 ( "tst",
                   CT_PTR CT_INT,
                   Some (FUNC_CALL ("malloc", [ LITERAL (CINT 16) ])) );
               VAR_DECL
                 ( "tst0",
                   CT_PTR CT_INT,
                   Some (FUNC_CALL ("malloc", [ LITERAL (CINT 1) ])) );
               EXPRESSION
                 (FUNC_CALL ("free", [ ADD (VAR_NAME "tst", LITERAL (CINT 1)) ]));
               EXPRESSION (FUNC_CALL ("free", [ VAR_NAME "tst0" ]));
             ] )
    >>= fun ctx ->
    declare_fun ctx
    @@ TOP_FUNC_DECL
         ( CT_INT,
           "main",
           [],
           BLOCK
             [
               (* VAR_DECL ("tst", CT_PTR (CT_STRUCT "node"), Some (LITERAL (CINT 1))); *)
               VAR_DECL ("a", CT_INT, Some (LITERAL (CINT 0)));
               VAR_DECL ("i", CT_INT, Some (LITERAL (CINT 0)));
               VAR_DECL
                 ( "arr",
                   CT_PTR (CT_PTR CT_INT),
                   Some (FUNC_CALL ("malloc", [ LITERAL (CINT 20) ])) );
               (*WHILE
                 ( LT (VAR_NAME "i", LITERAL (CINT 3)),
                   BLOCK
                     [
                       VAR_DECL ("a", CT_INT, Some (LITERAL (CINT 10)));
                       ASSIGN
                         (VAR_NAME "i", ADD (VAR_NAME "i", LITERAL (CINT 1)));
                     ] ); *)
               (* WHILE (LT (VAR_NAME "i", LITERAL (CINT 5)), BLOCK [
                    ASSIGN (DEREFERENCE (ADD (VAR_NAME "arr", VAR_NAME "i"  ) ),  FUNC_CALL ("malloc", [ LITERAL (CINT 20) ] ) );
                    ASSIGN (VAR_NAME "i", ADD (VAR_NAME "i", LITERAL (CINT 1)));
                  ] ); *)
               FOR
                 ( Some (VAR_DECL ("i", CT_INT, Some (LITERAL (CINT 0)))),
                   Some (LT (VAR_NAME "i", LITERAL (CINT 5))),
                   Some
                     (ASSIGN (VAR_NAME "i", ADD (VAR_NAME "i", LITERAL (CINT 1)))),
                   BLOCK
                     [
                       ASSIGN
                         ( DEREFERENCE (ADD (VAR_NAME "arr", VAR_NAME "i")),
                           FUNC_CALL ("malloc", [ LITERAL (CINT 20) ]) );
                     ] );
               (* ASSIGN ( DEREFERENCE (ADD (DEREFERENCE (ADD (VAR_NAME "arr", LITERAL (CINT 0))), LITERAL (CINT 1) ) ) , LITERAL (CINT 145) ); *)
               FOR
                 ( Some (VAR_DECL ("i", CT_INT, Some (LITERAL (CINT 0)))),
                   Some (LT (VAR_NAME "i", LITERAL (CINT 5))),
                   Some
                     (ASSIGN (VAR_NAME "i", ADD (VAR_NAME "i", LITERAL (CINT 1)))),
                   BLOCK
                     [
                       FOR
                         ( Some (VAR_DECL ("j", CT_INT, Some (LITERAL (CINT 0)))),
                           Some (LT (VAR_NAME "j", LITERAL (CINT 5))),
                           Some
                             (ASSIGN
                                ( VAR_NAME "j",
                                  ADD (VAR_NAME "j", LITERAL (CINT 1)) )),
                           BLOCK
                             [
                               (* ASSIGN (VAR_NAME "a", VAR_NAME "i"); *)
                               ASSIGN
                                 ( DEREFERENCE
                                     (ADD
                                        ( DEREFERENCE
                                            (ADD (VAR_NAME "arr", VAR_NAME "i")),
                                          VAR_NAME "j" )),
                                   LITERAL (CINT 145) );
                             ] );
                     ] );
               (*
                                     ASSIGN (
                                       DEREFERENCE (
                                         ADD (
                                           DEREFERENCE (ADD (VAR_NAME ("arr"), VAR_NAME ("i")))
                                         , VAR_NAME ("j")))
                                     , LITERAL (CINT (123))
                                    ) *)
               RETURN (LITERAL (CINT 1));
             ] )
    (*
       print_string @@ Result.get_ok Interpreterctx.E.test1;;
    *)
    >>=
    fun ctx ->
    let ctx' = { ctx with pack_addr = ctx.free_addr } in
    eval_stmt ctx' false false false CT_INT CT_VOID [ (max_int, max_int) ]
    @@ EXPRESSION (FUNC_CALL ("main", []))
    >>= fun (c, als) -> return @@ dbg_print c als

  let test0 =
    add_null (() |> make_exec_ctx) >>= fun ctx ->
    declare_fun ctx
    @@ TOP_FUNC_DECL
         ( CT_VOID,
           "ff",
           [ CARGS (CT_INT, "a") ],
           BLOCK
             [
               IF_ELSE
                 ( EQUAL (VAR_NAME "a", LITERAL (CINT 0)),
                   BLOCK [ RETURN (LITERAL (CINT 1)) ],
                   BLOCK
                     [
                       RETURN
                         (MUL
                            ( VAR_NAME "a",
                              FUNC_CALL
                                ("ff", [ SUB (VAR_NAME "a", LITERAL (CINT 1)) ])
                            ));
                     ] );
               VAR_DECL ("aa", CT_INT, None);
             ] )
    >>= fun ctx ->
    declare_struct ctx @@ TOP_STRUCT_DECL ("node1", [ CARGS (CT_INT, "value") ])
    >>= fun ctx ->
    declare_struct ctx @@ TOP_STRUCT_DECL ("node", [ CARGS (CT_INT, "value") ])
    >>= fun ctx ->
    declare_fun ctx
    @@ TOP_FUNC_DECL
         ( CT_STRUCT "node1",
           "fy",
           [],
           BLOCK
             [ VAR_DECL ("a", CT_STRUCT "node", None); RETURN (VAR_NAME "a") ]
         )
    >>= fun ctx ->
    declare_struct ctx
    @@ TOP_STRUCT_DECL ("rot", [ CARGS (CT_STRUCT "node", "value") ])
    >>= fun ctx ->
    declare_fun ctx
    @@ TOP_FUNC_DECL
         ( CT_PTR CT_VOID,
           "memcpy",
           [
             CARGS (CT_PTR CT_VOID, "dst");
             CARGS (CT_PTR CT_VOID, "src");
             CARGS (CT_INT, "len");
           ],
           BLOCK
             [
               VAR_DECL ("char_dst", CT_PTR CT_CHAR, Some (VAR_NAME "dst"));
               VAR_DECL ("char_src", CT_PTR CT_CHAR, Some (VAR_NAME "src"));
               VAR_DECL ("a", CT_INT, Some (LITERAL (CINT 0)));
               WHILE
                 ( LT (VAR_NAME "a", LITERAL (CINT 5)),
                   BLOCK
                     [
                       ASSIGN
                         ( DEREFERENCE (ADD (VAR_NAME "char_dst", VAR_NAME "a")),
                           DEREFERENCE (ADD (VAR_NAME "char_src", VAR_NAME "a"))
                         );
                       ASSIGN
                         (VAR_NAME "a", ADD (VAR_NAME "a", LITERAL (CINT 1)));
                     ] );
               RETURN (LITERAL (CINT 1));
             ] )
    >>= fun ctx ->
    (* declare_top ctx
       @@ TOP_VAR_DECL ("a", CT_INT, None)
       >>= fun ctx -> *)
    declare_fun ctx
    @@ TOP_FUNC_DECL
         ( CT_STRUCT "node",
           "fyf",
           [],
           BLOCK
             [ VAR_DECL ("a", CT_STRUCT "node1", None); RETURN (VAR_NAME "a") ]
         )
    >>= fun ctx ->
    declare_struct ctx
    @@ TOP_STRUCT_DECL ("list", [ CARGS (CT_PTR (CT_STRUCT "node"), "head") ])
    >>= fun ctx ->
    declare_fun ctx
    @@ TOP_FUNC_DECL
         (CT_VOID, "vf", [], BLOCK [ VAR_DECL ("a", CT_STRUCT "node1", None) ])
    >>= fun ctx ->
    declare_fun ctx
    @@ TOP_FUNC_DECL
         ( CT_INT,
           "main",
           [],
           BLOCK
             [
               VAR_DECL
                 ("tst", CT_PTR (CT_STRUCT "node"), Some (LITERAL (CINT 1)));
               RETURN (LITERAL (CINT 1));
             ] )
    >>= fun ctx ->
    let ctx' = { ctx with pack_addr = ctx.free_addr } in
    eval_stmt ctx' false false false CT_INT CT_VOID [ (max_int, max_int) ]
    @@ EXPRESSION (FUNC_CALL ("main", []))
    >>= fun (c, als) -> return @@ dbg_print c als

  let rec collect ctx stmts =
    match stmts with
    | [] -> return ctx
    | top :: tops -> (
        match top with
        | TOP_VAR_DECL _ ->
            declare_top ctx top >>= fun ctx' -> collect ctx' tops
        | TOP_FUNC_DECL _ ->
            declare_fun ctx top >>= fun ctx' -> collect ctx' tops
        | TOP_STRUCT_DECL _ ->
            declare_struct ctx top >>= fun ctx' -> collect ctx' tops
        | _ -> collect ctx tops (* eval' ctx palcs st *))

  let eval_d stmts vrs =
    add_null (() |> make_exec_ctx) >>= fun ctx ->
    collect ctx stmts >>= fun ct ->
    let ct = { ct with pack_addr = ct.free_addr } in
    eval_stmt ct false false false CT_INT CT_VOID [ (max_int, max_int) ]
    @@ EXPRESSION (FUNC_CALL ("main", []))
    >>= fun (ct, als) ->
    let vs =
      List.map
        (fun x ->
          get_from_vars ct x "can't find var" >>= function
          | _, _, hv -> return @@ get_val @@ Vhval hv)
        vrs
    in
    List.fold_left2
      (fun acc n xx ->
        xx >>= fun x ->
        acc >>= fun ac -> return @@ ac ^ n ^ " ~ " ^ show_v_value x ^ "\n")
      (return "") vrs vs

  (* return @@ dbg_print ct als *)
  (*
     print_string @@ Result.get_ok Interpreterctx.E.test0;;
  *)

  let eval_dd stmts vrs =
    add_null (() |> make_exec_ctx) >>= fun ctx ->
    collect ctx stmts >>= fun ct ->
    let ct = { ct with pack_addr = ct.free_addr } in
    eval_stmt ct false false false CT_INT CT_VOID [ (max_int, max_int) ]
    @@ EXPRESSION (FUNC_CALL ("main", []))
    >>= fun (ct, als) -> return @@ dbg_print ct als
  (*
     print_string @@ Result.get_ok Interpreterctx.E.test0;;
  *)
end

module E = Eval (Result)

let eval_d prg = E.eval_d prg

let eval_dd prg = E.eval_dd prg
