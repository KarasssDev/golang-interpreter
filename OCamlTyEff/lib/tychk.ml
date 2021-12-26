open Ast
open Format
open Bind

exception Incorrect_ty
exception Occurs_fail
exception Empty_macth
exception Matching_rebound (* inside pattern *)

type ty_map = ty BindMap.t
type effs_map = eff_set BindMap.t

let pp_ty_map = pp_bind_map pp_ty
let pp_effs_map = pp_bind_map pp_eff_set

type bind_set = BindSet.t

let pp_bind_set fmt set =
  pp_print_seq
    ~pp_sep:(fun fmt () -> fprintf fmt ", ")
    pp_print_string
    fmt
    (BindSet.to_seq set)
;;

type ty_chk_env =
  { decls : ty_map
  ; ty_bvars : bind_set
  ; eff_bvars : bind_set
  }
[@@deriving show { with_path = false }]

let concrete_effs effs env =
  EffSet.filter
    (function
      | EffVar name when is_not_bound name env.eff_bvars -> false
      | _ -> true)
    effs
;;

let var_effs effs env =
  List.of_seq
    (Seq.filter_map
       (function
         | EffVar name when is_not_bound name env.eff_bvars -> Some name
         | _ -> None)
       (EffSet.to_seq effs))
;;

let split_effs effs env = concrete_effs effs env, var_effs effs env

type subst =
  { ty : ty_map
  ; effs : effs_map
  }
[@@deriving show { with_path = false }]

let empty_subst = { ty = BindMap.empty; effs = BindMap.empty }
let ty_subst ty = { ty; effs = BindMap.empty }
let single_ty_subst name ty = ty_subst (BindMap.singleton name ty)

let double_ty_subst name1 name2 ty =
  ty_subst (BindMap.add name2 ty (BindMap.singleton name1 ty))
;;

let effs_subst effs = { ty = BindMap.empty; effs }
let single_effs_subst name ty = effs_subst (BindMap.singleton name ty)
let next_id = ref 0

let safe_name () =
  next_id := !next_id + 1;
  string_of_int !next_id
;;

let safe_tvar () = TVar (safe_name ())
let safe_eff_var () = EffVar (safe_name ())

let rec deduce_subst prm_ty arg_ty subst env =
  match prm_ty, arg_ty with
  | TInt, TInt | TString, TString | TBool, TBool | TTuple [], TTuple [] -> subst
  | TExc prm_exc, TExc arg_exc when equal_exc prm_exc arg_exc -> subst
  | TVar prm_bvar, TVar arg_bvar
    when is_bound prm_bvar env.ty_bvars
         && is_bound arg_bvar env.ty_bvars
         && prm_bvar = arg_bvar -> subst
  | TTuple prm_tys, TTuple arg_tys ->
    mrg_substs
      (List.map2
         (fun prm_ty arg_ty -> deduce_subst prm_ty arg_ty subst env)
         prm_tys
         arg_tys)
      env
  | TList arg_ty, TList prm_ty | TRef arg_ty, TRef prm_ty ->
    deduce_subst prm_ty arg_ty subst env
  | TFun (aa_ty, a_effs, ap_ty), TFun (pa_ty, p_effs, pp_ty) ->
    mrg_substs
      [ deduce_subst aa_ty pa_ty subst env
      ; deduce_subst pp_ty ap_ty subst env
      ; deduce_effs_subst p_effs a_effs subst env
      ]
      env
  | TVar prm_var, TVar arg_var
    when is_not_bound prm_var env.ty_bvars && is_not_bound arg_var env.ty_bvars ->
    if prm_var = arg_var
    then subst
    else (
      match BindMap.find_opt prm_var subst.ty, BindMap.find_opt arg_var subst.ty with
      | None, None -> mrg_subst subst (double_ty_subst prm_var arg_var (safe_tvar ())) env
      | Some ty, _ -> mrg_subst subst (single_ty_subst arg_var ty) env
      | None, Some ty -> mrg_subst subst (single_ty_subst prm_var ty) env)
  | TVar tvar, ty when is_not_bound tvar env.ty_bvars ->
    mrg_subst subst (single_ty_subst tvar ty) env
  | ty, TVar tvar when is_not_bound tvar env.ty_bvars ->
    mrg_subst subst (single_ty_subst tvar ty) env
  | _ -> raise Incorrect_ty

and deduce_effs_subst prm_effs arg_effs subst env =
  let prm_effs, arg_effs = EffSet.diff prm_effs arg_effs, EffSet.diff arg_effs prm_effs in
  let cp_effs, vp_effs = split_effs prm_effs env in
  let ca_effs, va_effs = split_effs arg_effs env in
  match vp_effs, va_effs with
  | _ :: _, _ :: _ ->
    let effs =
      Option.value
        ~default:(EffSet.singleton (safe_eff_var ()))
        (List.find_map (fun name -> BindMap.find_opt name subst.effs) (vp_effs @ va_effs))
    in
    let effs = EffSet.union effs (EffSet.union cp_effs ca_effs) in
    mrg_substs
      [ subst
      ; effs_subst
          (BindMap.of_seq (List.to_seq (List.map (fun k -> k, effs) (vp_effs @ va_effs))))
      ]
      env
  | [], _ when not (EffSet.is_empty ca_effs) -> raise Incorrect_ty
  | _, [] when not (EffSet.is_empty cp_effs) -> raise Incorrect_ty
  | _ ->
    mrg_substs
      [ subst
      ; effs_subst
          (BindMap.of_seq
             (List.to_seq
                (List.map (fun vp_eff -> vp_eff, ca_effs) vp_effs
                @ List.map (fun va_eff -> va_eff, cp_effs) va_effs)))
      ]
      env

and mrg_substs substs env =
  List.fold_left (fun acc subst -> mrg_subst acc subst env) empty_subst substs

and mrg_subst subst1 subst2 env =
  let subst =
    BindMap.fold
      (fun name ty subst ->
        match BindMap.find_opt name subst.ty with
        | None -> { subst with ty = BindMap.add name ty subst.ty }
        | Some ty2 -> deduce_subst ty ty2 subst env)
      subst2.ty
      subst1
  in
  BindMap.fold
    (fun name effs subst ->
      match BindMap.find_opt name subst.effs with
      | None -> { subst with effs = BindMap.add name effs subst.effs }
      | Some effs2 -> deduce_effs_subst effs effs2 subst env)
    subst2.effs
    subst
;;

let rec occurs_check name ty subst env =
  match ty with
  | TInt | TString | TBool | TExc _ -> ()
  | TTuple l -> List.iter (fun t -> occurs_check name t subst env) l
  | TList t | TRef t -> occurs_check name t subst env
  | TVar s when is_bound s env.ty_bvars -> ()
  | TVar s when s = name -> raise Occurs_fail
  | TVar s ->
    (match BindMap.find_opt s subst.ty with
    | None -> ()
    | Some t -> occurs_check name t subst env)
  | TFun (t1, _, t2) ->
    occurs_check name t1 subst env;
    occurs_check name t2 subst env
;;

let deduce_subst prm_ty arg_ty env =
  let subst = deduce_subst prm_ty arg_ty empty_subst env in
  BindMap.iter (fun name ty -> occurs_check name ty subst env) subst.ty;
  subst
;;

let rec get_effs_subst name subst env =
  match BindMap.find_opt name subst.effs with
  | None -> EffSet.singleton (EffVar name)
  | Some effs -> induce_effs_subst effs subst env

and induce_effs_subst effs subst env =
  EffSet.of_seq
    (Seq.flat_map
       (fun eff ->
         match eff with
         | EffVar name when is_not_bound name env.eff_bvars ->
           EffSet.to_seq (get_effs_subst name subst env)
         | _ -> List.to_seq [ eff ])
       (EffSet.to_seq effs))
;;

let rec get_ty_subst name subst env =
  match BindMap.find_opt name subst.ty with
  | None -> TVar name
  | Some (TVar name) when is_not_bound name env.ty_bvars -> get_ty_subst name subst env
  | Some ty -> ty
;;

let rec induce_subst ty subst env =
  match ty with
  | TInt | TString | TBool | TExc _ -> ty
  | TVar name when is_bound name env.ty_bvars -> ty
  | TTuple l -> TTuple (List.map (fun t -> induce_subst t subst env) l)
  | TList t -> TList (induce_subst t subst env)
  | TRef t -> TRef (induce_subst t subst env)
  | TVar name -> get_ty_subst name subst env
  | TFun (ty1, effs, ty2) ->
    TFun
      ( induce_subst ty1 subst env
      , induce_effs_subst effs subst env
      , induce_subst ty2 subst env )
;;

let all_eff_vars effs env =
  BindSet.of_list
    (List.filter_map
       (function
         | EffVar name when is_not_bound name env.eff_bvars -> Some name
         | _ -> None)
       (List.of_seq (EffSet.to_seq effs)))
;;

let rec all_ty_eff_vars ty env =
  match ty with
  | TInt | TString | TBool | TExc _ -> BindSet.empty, BindSet.empty
  | TVar name when is_bound name env.ty_bvars -> BindSet.empty, BindSet.empty
  | TTuple l ->
    List.fold_left
      (fun (tys1, effs1) t ->
        let tys2, effs2 = all_ty_eff_vars t env in
        BindSet.union tys1 tys2, BindSet.union effs1 effs2)
      (BindSet.empty, BindSet.empty)
      l
  | TList t | TRef t -> all_ty_eff_vars t env
  | TVar name -> BindSet.singleton name, BindSet.empty
  | TFun (ty1, effs, ty2) ->
    let tys1, effs1 = all_ty_eff_vars ty1 env in
    let tys2, effs2 = all_ty_eff_vars ty2 env in
    ( BindSet.union tys1 tys2
    , BindSet.union (all_eff_vars effs env) (BindSet.union effs1 effs2) )
;;

let safe_subst ty env =
  let tys, effs = all_ty_eff_vars ty env in
  { ty =
      BindSet.fold (fun name map -> BindMap.add name (safe_tvar ()) map) tys BindMap.empty
  ; effs =
      BindSet.fold
        (fun name map -> BindMap.add name (EffSet.singleton (safe_eff_var ())) map)
        effs
        BindMap.empty
  }
;;

let safe_ty ty env = induce_subst ty (safe_subst ty env) env

let safe_effs effs env =
  EffSet.map
    (function
      | EffVar name when is_not_bound name env.eff_bvars -> safe_eff_var ()
      | eff -> eff)
    effs
;;

let safe_ty_effs (ty, effs) env = safe_ty ty env, safe_effs effs env

let mrg_decls decls1 decls2 =
  BindMap.merge
    (fun (_ : string) ty1 ty2 ->
      match ty1, ty2 with
      | Some _, Some _ -> raise Matching_rebound
      | None, None -> None
      | Some ty, None | None, Some ty -> Some ty)
    decls1
    decls2
;;

let rec case_decls ty ptrn =
  match ptrn, ty with
  | PVal name, _ -> BindMap.singleton name ty
  | PConst (CInt _), TInt
  | PConst (CString _), TString
  | PConst (CBool _), TBool
  | PConst CEmptyList, TList _ -> BindMap.empty
  | PTuple ptrns, TTuple tys ->
    List.fold_left2
      (fun decls t p -> mrg_decls decls (case_decls t p))
      BindMap.empty
      tys
      ptrns
  | PCons (ptrns, ptrn), TList ty ->
    List.fold_left
      (fun decls p -> mrg_decls decls (case_decls ty p))
      (case_decls (TList ty) ptrn)
      ptrns
  | _ -> raise Incorrect_ty
;;

let case_env ty ptrn env =
  { env with decls = BindMap.add_seq (BindMap.to_seq (case_decls ty ptrn)) env.decls }
;;

let check_assignable decl_ty val_ty env =
  let new_ty_bvars, new_eff_bvars = all_ty_eff_vars decl_ty env in
  let bind_env =
    { env with
      eff_bvars = BindSet.add_seq (BindSet.to_seq new_eff_bvars) env.eff_bvars
    ; ty_bvars = BindSet.add_seq (BindSet.to_seq new_ty_bvars) env.ty_bvars
    }
  in
  let _ = deduce_subst decl_ty val_ty bind_env in
  ()
;;

let rec infer_ty_effs env expr =
  safe_ty_effs
    (match expr with
    | EConst const ->
      ( (match const with
        | CInt _ -> TInt
        | CString _ -> TString
        | CBool _ -> TBool
        | CEmptyList -> TList (safe_tvar ()))
      , EffSet.empty )
    | EVal name -> find_bind env.decls name, EffSet.empty
    | EUnop (op, expr) ->
      let ty, effs = infer_ty_effs env expr in
      (match op, ty with
      | Neg, TInt -> TInt, effs
      | Deref, TRef t -> t, effs
      | _ -> raise Incorrect_ty)
    | EBinop (expr1, op, expr2) ->
      let ty1, effs1 = infer_ty_effs env expr1 in
      let ty2, effs2 = infer_ty_effs env expr2 in
      let effs = EffSet.union effs1 effs2 in
      (match ty1, op, ty2 with
      | TInt, Add, TInt | TInt, Sub, TInt | TInt, Mul, TInt | TInt, Div, TInt ->
        TInt, effs
      | TInt, Eq, TInt
      | TInt, Neq, TInt
      | TInt, Les, TInt
      | TInt, Leq, TInt
      | TInt, Gre, TInt
      | TInt, Geq, TInt
      | TString, Eq, TString
      | TString, Neq, TString
      | TBool, Eq, TBool
      | TBool, Neq, TBool
      | TBool, And, TBool
      | TBool, Or, TBool -> TBool, effs
      | TRef ref_ty, Asgmt, val_ty ->
        check_assignable ref_ty val_ty env;
        TTuple [], EffSet.add EffAsgmt effs
      | ty, Cons, TList lty ->
        induce_subst (TList lty) (deduce_subst lty ty env) env, effs
      | _ -> raise Incorrect_ty)
    | EApp (f, arg) ->
      let f_ty, f_effs = infer_ty_effs env f in
      let arg_ty, arg_effs = infer_ty_effs env arg in
      (match f_ty with
      | TFun (prm_ty, effs, ret_ty) ->
        let subst = deduce_subst prm_ty arg_ty env in
        ( induce_subst ret_ty subst env
        , EffSet.union (EffSet.union f_effs arg_effs) (induce_effs_subst effs subst env) )
      | _ -> raise Incorrect_ty)
    | ETuple exprs ->
      let tys, effss = List.split (List.map (fun e -> infer_ty_effs env e) exprs) in
      TTuple tys, List.fold_left (fun e1 e2 -> EffSet.union e1 e2) EffSet.empty effss
    | ELet (decl, expr) ->
      let decl_ty = safe_ty decl.ty env in
      let new_env = { env with decls = BindMap.add decl.name decl_ty env.decls } in
      let val_ty, val_effs =
        infer_ty_effs (if decl.is_rec then new_env else env) decl.expr
      in
      check_assignable decl_ty val_ty env;
      let ty, effs = infer_ty_effs new_env expr in
      ty, EffSet.union val_effs effs
    | EMatch (scr, ptrns) ->
      let scr_ty, scr_effs = infer_ty_effs env scr in
      (match ptrns with
      | [] -> raise Empty_macth
      | (ptrn1, case1) :: cases ->
        let ty, effs = infer_ty_effs (case_env scr_ty ptrn1 env) case1 in
        List.fold_left
          (fun (ty, effs) (ptrn, case) ->
            let ty2, effs2 = infer_ty_effs (case_env scr_ty ptrn env) case in
            induce_subst ty (deduce_subst ty ty2 env) env, EffSet.union effs effs2)
          (ty, EffSet.union scr_effs effs)
          cases)
    | EFun (arg, arg_ty, expr) ->
      let new_ty_bvars, new_eff_bvars = all_ty_eff_vars arg_ty env in
      let env =
        { decls = BindMap.add arg arg_ty env.decls
        ; eff_bvars = BindSet.add_seq (BindSet.to_seq new_eff_bvars) env.eff_bvars
        ; ty_bvars = BindSet.add_seq (BindSet.to_seq new_ty_bvars) env.ty_bvars
        }
      in
      let ret_ty, effs = infer_ty_effs env expr in
      TFun (arg_ty, effs, ret_ty), EffSet.empty
    | ETry (scr, excs) ->
      let scr_ty, scr_effs = infer_ty_effs env scr in
      let ty, effs =
        List.fold_left
          (fun (ty, effs) (_, case) ->
            let ty2, effs2 = infer_ty_effs env case in
            induce_subst ty (deduce_subst ty ty2 env) env, EffSet.union effs effs2)
          (scr_ty, EffSet.empty)
          excs
      in
      ( ty
      , EffSet.union
          (EffSet.diff
             scr_effs
             (EffSet.of_list (List.map (fun (exc, _) -> EffExc exc) excs)))
          effs ))
    env
;;

let empty_ty_chk_env =
  { decls = BindMap.empty; ty_bvars = BindSet.empty; eff_bvars = BindSet.empty }
;;

let stdlib_ty_chk_env =
  { empty_ty_chk_env with
    decls =
      BindMap.of_seq
        (List.to_seq
           (List.map
              (fun (name, ty) -> name, safe_ty ty empty_ty_chk_env)
              [ "println", TFun (TString, EffSet.singleton EffIO, TTuple [])
              ; "raise1", TFun (TTuple [], EffSet.singleton (EffExc Exc1), TVar "a")
              ; "raise2", TFun (TTuple [], EffSet.singleton (EffExc Exc2), TVar "a")
              ; "ref", TFun (TVar "a", EffSet.empty, TRef (TVar "a"))
              ; ( "sneaky_eff"
                , TFun
                    ( TFun (TVar "a", EffSet.singleton (EffVar "e"), TVar "b")
                    , EffSet.empty
                    , TFun (TVar "a", EffSet.singleton (EffVar "e2"), TVar "b") ) )
              ]))
  }
;;

let check_program =
  List.fold_left
    (fun env (decl : decl) ->
      let decl_ty = safe_ty decl.ty env in
      let new_env = { env with decls = BindMap.add decl.name decl_ty env.decls } in
      let val_ty, _ = infer_ty_effs (if decl.is_rec then new_env else env) decl.expr in
      check_assignable decl_ty val_ty env;
      new_env)
    stdlib_ty_chk_env
;;

(* Tests *)

let test_infer_tyeffs expr matcher =
  let ty, effs = infer_ty_effs stdlib_ty_chk_env expr in
  let result = matcher (ty, effs) in
  if result then () else printf "Actual:\nty=%a\neffs=%a\n" pp_ty ty pp_eff_set effs;
  result
;;

let test_infer_tyeffs_eq expr ty effs =
  test_infer_tyeffs expr
  @@ fun (ty2, effs2) -> equal_ty ty ty2 && equal_eff_set effs effs2
;;

(*
let rec map : ('a -['e]-> 'b) --> 'a list -['e]-> 'b list = fun f: ('a -['e]-> 'b) -> fun xs : 'a list ->
  match xs with
  | [] -> []
  | x::xs -> (f x) :: (map f xs) in
let id: 'a --> 'a = fun x: 'a -> x in
map id
*)
let%test _ =
  test_infer_tyeffs
    (ELet
       ( { is_rec = true
         ; name = "map"
         ; ty =
             TFun
               ( TFun (TVar "a", EffSet.of_list [ EffVar "e" ], TVar "b")
               , EffSet.of_list []
               , TFun (TList (TVar "a"), EffSet.of_list [ EffVar "e" ], TList (TVar "b"))
               )
         ; expr =
             EFun
               ( "f"
               , TFun (TVar "a", EffSet.of_list [ EffVar "e" ], TVar "b")
               , EFun
                   ( "xs"
                   , TList (TVar "a")
                   , EMatch
                       ( EVal "xs"
                       , [ PConst CEmptyList, EConst CEmptyList
                         ; ( PCons ([ PVal "x" ], PVal "xs")
                           , EBinop
                               ( EApp (EVal "f", EVal "x")
                               , Cons
                               , EApp (EApp (EVal "map", EVal "f"), EVal "xs") ) )
                         ] ) ) )
         }
       , ELet
           ( { is_rec = false
             ; name = "id"
             ; ty = TFun (TVar "a", EffSet.of_list [], TVar "a")
             ; expr = EFun ("x", TVar "a", EVal "x")
             }
           , EApp (EVal "map", EVal "id") ) ))
  @@ function
  | TFun (TList (TVar v1), effs1, TList (TVar v2)), effs2 ->
    v1 = v2 && EffSet.is_empty effs1 && EffSet.is_empty effs2
  | _ -> false
;;

(*
let rec map : ('a -['e]-> 'b) --> 'a list -['e]-> 'b list = fun (f: 'a -['e]-> 'b) -> fun xs : 'a list ->
  match xs with
  | [] -> []
  | x::xs -> (f x) :: (map f xs) in
map (fun n: int -> let o: () = println "hi" in n + 1)
*)
let%test _ =
  test_infer_tyeffs_eq
    (ELet
       ( { is_rec = true
         ; name = "map"
         ; ty =
             TFun
               ( TFun (TVar "a", EffSet.of_list [ EffVar "e" ], TVar "b")
               , EffSet.of_list []
               , TFun (TList (TVar "a"), EffSet.of_list [ EffVar "e" ], TList (TVar "b"))
               )
         ; expr =
             EFun
               ( "f"
               , TFun (TVar "a", EffSet.of_list [ EffVar "e" ], TVar "b")
               , EFun
                   ( "xs"
                   , TList (TVar "a")
                   , EMatch
                       ( EVal "xs"
                       , [ PConst CEmptyList, EConst CEmptyList
                         ; ( PCons ([ PVal "x" ], PVal "xs")
                           , EBinop
                               ( EApp (EVal "f", EVal "x")
                               , Cons
                               , EApp (EApp (EVal "map", EVal "f"), EVal "xs") ) )
                         ] ) ) )
         }
       , EApp
           ( EVal "map"
           , EFun
               ( "n"
               , TInt
               , ELet
                   ( { is_rec = false
                     ; name = "o"
                     ; ty = TTuple []
                     ; expr = EApp (EVal "println", EConst (CString "hi"))
                     }
                   , EBinop (EVal "n", Add, EConst (CInt 1)) ) ) ) ))
    (TFun (TList TInt, EffSet.of_list [ EffIO ], TList TInt))
    EffSet.empty
;;

(*
let rec map2 : ('a --> 'b -['e]-> 'c) --> 'a list --> 'b list -['e, exc Exc1]-> 'c list = 
  fun f: ('a --> 'b -['e]-> 'c) ->
    fun l1: 'a list -> fun l2: 'b list ->
  match (l1, l2) with
  | ([], []) -> []
  | (a1::l1, a2::l2) -> let r: 'c = f a1 a2 in r :: map2 f l1 l2
  | (o1, o2) -> raise1 ()
in
map2 (fun n: int -> fun m: 'a -> n)
*)

let%test _ =
  test_infer_tyeffs
    (ELet
       ( { is_rec = true
         ; name = "map2"
         ; ty =
             TFun
               ( TFun
                   ( TVar "a"
                   , EffSet.of_list []
                   , TFun (TVar "b", EffSet.of_list [ EffVar "e" ], TVar "c") )
               , EffSet.of_list []
               , TFun
                   ( TList (TVar "a")
                   , EffSet.of_list []
                   , TFun
                       ( TList (TVar "b")
                       , EffSet.of_list [ EffExc Exc1; EffVar "e" ]
                       , TList (TVar "c") ) ) )
         ; expr =
             EFun
               ( "f"
               , TFun
                   ( TVar "a"
                   , EffSet.of_list []
                   , TFun (TVar "b", EffSet.of_list [ EffVar "e" ], TVar "c") )
               , EFun
                   ( "l1"
                   , TList (TVar "a")
                   , EFun
                       ( "l2"
                       , TList (TVar "b")
                       , EMatch
                           ( ETuple [ EVal "l1"; EVal "l2" ]
                           , [ ( PTuple [ PConst CEmptyList; PConst CEmptyList ]
                               , EConst CEmptyList )
                             ; ( PTuple
                                   [ PCons ([ PVal "a1" ], PVal "l1")
                                   ; PCons ([ PVal "a2" ], PVal "l2")
                                   ]
                               , ELet
                                   ( { is_rec = false
                                     ; name = "r"
                                     ; ty = TVar "c"
                                     ; expr = EApp (EApp (EVal "f", EVal "a1"), EVal "a2")
                                     }
                                   , EBinop
                                       ( EVal "r"
                                       , Cons
                                       , EApp
                                           ( EApp (EApp (EVal "map2", EVal "f"), EVal "l1")
                                           , EVal "l2" ) ) ) )
                             ; ( PTuple [ PVal "o1"; PVal "o2" ]
                               , EApp (EVal "raise1", ETuple []) )
                             ] ) ) ) )
         }
       , EApp (EVal "map2", EFun ("n", TInt, EFun ("m", TVar "a", EVal "n"))) ))
  @@ function
  | TFun (TList TInt, effs1, TFun (TList (TVar _), effs2, TList TInt)), effs3 ->
    EffSet.is_empty effs1
    && equal_eff_set effs2 (EffSet.singleton (EffExc Exc1))
    && EffSet.is_empty effs3
  | _ -> false
;;

(*
let rec map2 : ('a --> 'b -['e]-> 'c) --> 'a list --> 'b list -['e, exc Exc1]-> 'c list = 
  fun f: ('a --> 'b -['e]-> 'c) ->
    fun l1: 'a list -> fun l2: 'b list ->
  match (l1, l2) with
  | ([], []) -> []
  | (a1::l1, a2::l2) -> let r: 'c = f a1 a2 in r :: map2 f l1 l2
  | (o1, o2) -> raise1 ()
in
map2 (fun n: int -> fun m: 'a -> raise2 ()) (1 :: [])
*)
let%test _ =
  test_infer_tyeffs
    (ELet
       ( { is_rec = true
         ; name = "map2"
         ; ty =
             TFun
               ( TFun
                   ( TVar "a"
                   , EffSet.of_list []
                   , TFun (TVar "b", EffSet.of_list [ EffVar "e" ], TVar "c") )
               , EffSet.of_list []
               , TFun
                   ( TList (TVar "a")
                   , EffSet.of_list []
                   , TFun
                       ( TList (TVar "b")
                       , EffSet.of_list [ EffExc Exc1; EffVar "e" ]
                       , TList (TVar "c") ) ) )
         ; expr =
             EFun
               ( "f"
               , TFun
                   ( TVar "a"
                   , EffSet.of_list []
                   , TFun (TVar "b", EffSet.of_list [ EffVar "e" ], TVar "c") )
               , EFun
                   ( "l1"
                   , TList (TVar "a")
                   , EFun
                       ( "l2"
                       , TList (TVar "b")
                       , EMatch
                           ( ETuple [ EVal "l1"; EVal "l2" ]
                           , [ ( PTuple [ PConst CEmptyList; PConst CEmptyList ]
                               , EConst CEmptyList )
                             ; ( PTuple
                                   [ PCons ([ PVal "a1" ], PVal "l1")
                                   ; PCons ([ PVal "a2" ], PVal "l2")
                                   ]
                               , ELet
                                   ( { is_rec = false
                                     ; name = "r"
                                     ; ty = TVar "c"
                                     ; expr = EApp (EApp (EVal "f", EVal "a1"), EVal "a2")
                                     }
                                   , EBinop
                                       ( EVal "r"
                                       , Cons
                                       , EApp
                                           ( EApp (EApp (EVal "map2", EVal "f"), EVal "l1")
                                           , EVal "l2" ) ) ) )
                             ; ( PTuple [ PVal "o1"; PVal "o2" ]
                               , EApp (EVal "raise1", ETuple []) )
                             ] ) ) ) )
         }
       , EApp
           ( EApp
               ( EVal "map2"
               , EFun ("n", TInt, EFun ("m", TVar "a", EApp (EVal "raise2", ETuple [])))
               )
           , EBinop (EConst (CInt 1), Cons, EConst CEmptyList) ) ))
  @@ function
  | TFun (TList (TVar _), effs1, TList (TVar _)), effs2 ->
    equal_eff_set effs1 (EffSet.of_list [ EffExc Exc1; EffExc Exc2 ])
    && EffSet.is_empty effs2
  | _ -> false
;;

(*
try raise1 () with
| Exc1 -> 1
*)
let%test _ =
  test_infer_tyeffs (ETry (EApp (EVal "raise1", ETuple []), [ Exc1, EConst (CInt 1) ]))
  @@ function
  | TInt, effs -> EffSet.is_empty effs
  | _ -> false
;;

(*
try raise1 () with
| Exc1 -> raise2 ()
*)
let%test _ =
  test_infer_tyeffs
    (ETry (EApp (EVal "raise1", ETuple []), [ Exc1, EApp (EVal "raise2", ETuple []) ]))
  @@ function
  | TVar _, effs -> equal_eff_set effs (EffSet.singleton (EffExc Exc2))
  | _ -> false
;;

(*
try raise1 () with
| Exc1 -> raise1 ()
*)
let%test _ =
  test_infer_tyeffs
    (ETry (EApp (EVal "raise1", ETuple []), [ Exc1, EApp (EVal "raise1", ETuple []) ]))
  @@ function
  | TVar _, effs -> equal_eff_set effs (EffSet.singleton (EffExc Exc1))
  | _ -> false
;;

(*
let f: bool -[exc Exc1, exc Exc2]-> string = fun flag: bool ->
  match flag with
  | true -> raise1 ()
  | false -> raise2 ()
in
try f true with
| Exc1 -> raise2 ()
| Exc2 -> "literal"
*)
let%test _ =
  test_infer_tyeffs
    (ELet
       ( { is_rec = false
         ; name = "f"
         ; ty = TFun (TBool, EffSet.of_list [ EffExc Exc1; EffExc Exc2 ], TString)
         ; expr =
             EFun
               ( "flag"
               , TBool
               , EMatch
                   ( EVal "flag"
                   , [ PConst (CBool true), EApp (EVal "raise1", ETuple [])
                     ; PConst (CBool false), EApp (EVal "raise2", ETuple [])
                     ] ) )
         }
       , ETry
           ( EApp (EVal "f", EConst (CBool true))
           , [ Exc1, EApp (EVal "raise2", ETuple []); Exc2, EConst (CString "literal") ]
           ) ))
  @@ function
  | TString, effs -> equal_eff_set effs (EffSet.singleton (EffExc Exc2))
  | _ -> false
;;

(*
let rec fix: (('a -['e]-> 'b) --> 'a -['e]-> 'b) --> 'a -['e]-> 'b = 
  fun (f: ('a -['e]-> 'b) --> 'a -['e]-> 'b) -> fun eta: 'a -> f (fix f) eta
in
let fac: (int --> int) --> int --> int = fun self: (int --> int) -> fun n: int -> 
  match n <= 1 with
  | true -> 1
  | false -> n * (self (n-1))
in
fix fac
*)
let%test _ =
  test_infer_tyeffs
    (ELet
       ( { is_rec = true
         ; name = "fix"
         ; ty =
             TFun
               ( TFun
                   ( TFun (TVar "a", EffSet.of_list [ EffVar "e" ], TVar "b")
                   , EffSet.of_list []
                   , TFun (TVar "a", EffSet.of_list [ EffVar "e" ], TVar "b") )
               , EffSet.of_list []
               , TFun (TVar "a", EffSet.of_list [ EffVar "e" ], TVar "b") )
         ; expr =
             EFun
               ( "f"
               , TFun
                   ( TFun (TVar "a", EffSet.of_list [ EffVar "e" ], TVar "b")
                   , EffSet.of_list []
                   , TFun (TVar "a", EffSet.of_list [ EffVar "e" ], TVar "b") )
               , EFun
                   ( "eta"
                   , TVar "a"
                   , EApp (EApp (EVal "f", EApp (EVal "fix", EVal "f")), EVal "eta") ) )
         }
       , ELet
           ( { is_rec = false
             ; name = "fac"
             ; ty =
                 TFun
                   ( TFun (TInt, EffSet.of_list [], TInt)
                   , EffSet.of_list []
                   , TFun (TInt, EffSet.of_list [], TInt) )
             ; expr =
                 EFun
                   ( "self"
                   , TFun (TInt, EffSet.of_list [], TInt)
                   , EFun
                       ( "n"
                       , TInt
                       , EMatch
                           ( EBinop (EVal "n", Leq, EConst (CInt 1))
                           , [ PConst (CBool true), EConst (CInt 1)
                             ; ( PConst (CBool false)
                               , EBinop
                                   ( EVal "n"
                                   , Mul
                                   , EApp
                                       ( EVal "self"
                                       , EBinop (EVal "n", Sub, EConst (CInt 1)) ) ) )
                             ] ) ) )
             }
           , EApp (EVal "fix", EVal "fac") ) ))
  @@ function
  | TFun (TInt, effs1, TInt), effs2 -> EffSet.is_empty effs1 && EffSet.is_empty effs2
  | _ -> false
;;

(*
(fun (f : ('a -['e]-> 'b) --> 'a -['e]-> 'b) ->
  let r : ('a -['e]-> 'b) ref = ref (fun o : 'a -> (sneaky_eff raise1) ()) in
  let fixf : 'a -['e]-> 'b = fun x : 'a -> f !r x in
  let o: () = r := fixf in
  !r)
(fun (self: string list -[IO]-> ()) -> fun l: string list -> match l with
| hd::tl -> let o: unit = println hd in self tl
| o -> ())
*)
let%test _ =
  test_infer_tyeffs_eq
    (EApp
       ( EFun
           ( "f"
           , TFun
               ( TFun (TVar "a", EffSet.of_list [ EffVar "e" ], TVar "b")
               , EffSet.of_list []
               , TFun (TVar "a", EffSet.of_list [ EffVar "e" ], TVar "b") )
           , ELet
               ( { is_rec = false
                 ; name = "r"
                 ; ty = TRef (TFun (TVar "a", EffSet.of_list [ EffVar "e" ], TVar "b"))
                 ; expr =
                     EApp
                       ( EVal "ref"
                       , EFun
                           ( "o"
                           , TVar "a"
                           , EApp (EApp (EVal "sneaky_eff", EVal "raise1"), ETuple []) )
                       )
                 }
               , ELet
                   ( { is_rec = false
                     ; name = "fixf"
                     ; ty = TFun (TVar "a", EffSet.of_list [ EffVar "e" ], TVar "b")
                     ; expr =
                         EFun
                           ( "x"
                           , TVar "a"
                           , EApp (EApp (EVal "f", EUnop (Deref, EVal "r")), EVal "x") )
                     }
                   , ELet
                       ( { is_rec = false
                         ; name = "o"
                         ; ty = TTuple []
                         ; expr = EBinop (EVal "r", Asgmt, EVal "fixf")
                         }
                       , EUnop (Deref, EVal "r") ) ) ) )
       , EFun
           ( "self"
           , TFun (TList TString, EffSet.of_list [ EffIO ], TTuple [])
           , EFun
               ( "l"
               , TList TString
               , EMatch
                   ( EVal "l"
                   , [ ( PCons ([ PVal "hd" ], PVal "tl")
                       , ELet
                           ( { is_rec = false
                             ; name = "o"
                             ; ty = TTuple []
                             ; expr = EApp (EVal "println", EVal "hd")
                             }
                           , EApp (EVal "self", EVal "tl") ) )
                     ; PVal "o", ETuple []
                     ] ) ) ) ))
    (TFun (TList TString, EffSet.of_list [ EffIO ], TTuple []))
    (EffSet.singleton EffAsgmt)
;;

(* 1 + 1 *)
let%test _ =
  test_infer_tyeffs_eq (EBinop (EConst (CInt 1), Add, EConst (CInt 1))) TInt EffSet.empty
;;

(* 1 - 1 *)
let%test _ =
  test_infer_tyeffs_eq (EBinop (EConst (CInt 1), Sub, EConst (CInt 1))) TInt EffSet.empty
;;

(* 1 * 1 *)
let%test _ =
  test_infer_tyeffs_eq (EBinop (EConst (CInt 1), Mul, EConst (CInt 1))) TInt EffSet.empty
;;

(* 1 / 1 *)
let%test _ =
  test_infer_tyeffs_eq (EBinop (EConst (CInt 1), Div, EConst (CInt 1))) TInt EffSet.empty
;;

(* 1 = 1 *)
let%test _ =
  test_infer_tyeffs_eq (EBinop (EConst (CInt 1), Eq, EConst (CInt 1))) TBool EffSet.empty
;;

(* 1 != 1 *)
let%test _ =
  test_infer_tyeffs_eq (EBinop (EConst (CInt 1), Neq, EConst (CInt 1))) TBool EffSet.empty
;;

(* 1 < 1 *)
let%test _ =
  test_infer_tyeffs_eq (EBinop (EConst (CInt 1), Les, EConst (CInt 1))) TBool EffSet.empty
;;

(* 1 <= 1 *)
let%test _ =
  test_infer_tyeffs_eq (EBinop (EConst (CInt 1), Leq, EConst (CInt 1))) TBool EffSet.empty
;;

(* 1 > 1 *)
let%test _ =
  test_infer_tyeffs_eq (EBinop (EConst (CInt 1), Gre, EConst (CInt 1))) TBool EffSet.empty
;;

(* 1 >= 1 *)
let%test _ =
  test_infer_tyeffs_eq (EBinop (EConst (CInt 1), Geq, EConst (CInt 1))) TBool EffSet.empty
;;

(* "s" = "s" *)
let%test _ =
  test_infer_tyeffs_eq
    (EBinop (EConst (CString "s"), Eq, EConst (CString "s")))
    TBool
    EffSet.empty
;;

(* "s" != "s" *)
let%test _ =
  test_infer_tyeffs_eq
    (EBinop (EConst (CString "s"), Neq, EConst (CString "s")))
    TBool
    EffSet.empty
;;

(* true = false *)
let%test _ =
  test_infer_tyeffs_eq
    (EBinop (EConst (CBool true), Eq, EConst (CBool false)))
    TBool
    EffSet.empty
;;

(* true != false *)
let%test _ =
  test_infer_tyeffs_eq
    (EBinop (EConst (CBool true), Neq, EConst (CBool false)))
    TBool
    EffSet.empty
;;

(* true && false *)
let%test _ =
  test_infer_tyeffs_eq
    (EBinop (EConst (CBool true), And, EConst (CBool false)))
    TBool
    EffSet.empty
;;

(* true || false *)
let%test _ =
  test_infer_tyeffs_eq
    (EBinop (EConst (CBool true), Or, EConst (CBool false)))
    TBool
    EffSet.empty
;;

(* (ref 1) := 2 *)
let%test _ =
  test_infer_tyeffs_eq
    (EBinop (EApp (EVal "ref", EConst (CInt 1)), Asgmt, EConst (CInt 2)))
    (TTuple [])
    (EffSet.singleton EffAsgmt)
;;

(* 1 :: [] *)
let%test _ =
  test_infer_tyeffs_eq
    (EBinop (EConst (CInt 1), Cons, EConst CEmptyList))
    (TList TInt)
    EffSet.empty
;;

(* !(ref 1) *)
let%test _ =
  test_infer_tyeffs_eq
    (EUnop (Deref, EApp (EVal "ref", EConst (CInt 1))))
    TInt
    EffSet.empty
;;

(* -(1) *)
let%test _ = test_infer_tyeffs_eq (EUnop (Neg, EConst (CInt 1))) TInt EffSet.empty
