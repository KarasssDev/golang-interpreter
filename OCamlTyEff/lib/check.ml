open Ast
open Format
open Printexc
module BindMap = Map.Make (String)
module BindSet = Set.Make (String)

type ty_map = ty BindMap.t
type effs_map = eff_set BindMap.t

exception Incorrect_ty
exception Occurs_fail
exception Not_bound of string
exception Empty_macth
exception Matching_rebound

let find_bind map name =
  try BindMap.find name map with
  | Not_found -> raise (Not_bound name)
;;

let is_bound set name =
  try
    let _ = BindSet.find set name in
    true
  with
  | Not_found -> false
;;

let pp_ty_map fmt map =
  BindMap.fold
    (fun k v _ ->
      Format.fprintf fmt "%s=" k;
      pp_ty fmt v;
      Format.fprintf fmt "\n")
    map
    ()
;;

let pp_effs_map fmt map =
  BindMap.fold
    (fun k v _ ->
      Format.fprintf fmt "%s=" k;
      pp_eff_set fmt v;
      Format.fprintf fmt "\n")
    map
    ()
;;

let concrete_effs =
  EffSet.filter (function
      | EffVar _ -> false
      | _ -> true)
;;

let eff_vars effs =
  List.of_seq
    (Seq.filter_map
       (function
         | EffVar name -> Some name
         | _ -> None)
       (EffSet.to_seq effs))
;;

let split_effs effs = concrete_effs effs, eff_vars effs

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

let double_effs_subst name1 name2 ty =
  effs_subst (BindMap.add name2 ty (BindMap.singleton name1 ty))
;;

let next_id = ref 0

let safe_tvar_name name =
  next_id := !next_id + 1;
  string_of_int !next_id
;;

(* ^ string_of_int (Random.bits ())
  ^ string_of_int (Random.bits ())
  ^ string_of_int (Random.bits ())
  ^ string_of_int (Random.bits ()) *)

let rec deduce_subst prmty argty subst =
  (* Format.fprintf std_formatter "\nprmty=";
  pp_ty std_formatter prmty;
  Format.fprintf std_formatter "\nargty=";
  pp_ty std_formatter argty;
  Format.fprintf std_formatter "\nsubst=";
  pp_subst std_formatter subst;
  Format.fprintf std_formatter "\n"; *)
  match prmty, argty with
  | TInt, TInt | TString, TString | TBool, TBool | TTuple [], TTuple [] -> subst
  | TExc prmexc, TExc argexc when equal_exc prmexc argexc -> subst
  | TBoundVar prmbvar, TBoundVar argbvar when prmbvar = argbvar -> subst
  | TTuple prmtys, TTuple argtys ->
    mrg_substs
      (List.map2 (fun prmty argty -> deduce_subst prmty argty subst) prmtys argtys)
  | TList argty, TList prmty | TRef argty, TRef prmty -> deduce_subst argty prmty subst
  | TFun (aaty, aeffs, apty), TFun (paty, peffs, ppty) ->
    mrg_substs
      [ deduce_subst aaty paty subst
      ; deduce_subst ppty apty subst
      ; deduce_effs_subst peffs aeffs subst
      ]
  | TVar pname, TVar aname when pname = aname -> subst
  | TBoundVar pname, TBoundVar aname when pname = aname -> subst
  | TVar pname, TVar aname ->
    (match BindMap.find_opt pname subst.ty, BindMap.find_opt aname subst.ty with
    | None, None ->
      mrg_subst
        subst
        (double_ty_subst pname aname (TVar (safe_tvar_name (pname ^ " " ^ aname))))
    | Some ty, _ -> mrg_subst subst (single_ty_subst aname ty)
    | None, Some ty -> mrg_subst subst (single_ty_subst pname ty))
  | TVar name, ty | ty, TVar name -> mrg_subst subst (single_ty_subst name ty)
  | _ ->
    printf "\nargty=";
    pp_ty std_formatter argty;
    printf "\nprmty=";
    pp_ty std_formatter prmty;
    raise Incorrect_ty

and deduce_effs_subst peffs aeffs subst =
  let peffs, aeffs = EffSet.diff peffs aeffs, EffSet.diff aeffs peffs in
  let cpeffs, vpeffs = split_effs peffs in
  let caeffs, vaeffs = split_effs aeffs in
  match vpeffs, vaeffs with
  | _ :: _, _ :: _ ->
    let effs =
      Option.value
        ~default:
          (EffSet.singleton
             (EffVar (safe_tvar_name (String.concat " " (vpeffs @ vaeffs)))))
        (List.find_map (fun name -> BindMap.find_opt name subst.effs) (vpeffs @ vaeffs))
    in
    let effs = EffSet.union effs (EffSet.union cpeffs caeffs) in
    mrg_substs
      [ subst
      ; effs_subst
          (BindMap.of_seq (List.to_seq (List.map (fun k -> k, effs) (vpeffs @ vaeffs))))
      ]
  | [], _ when not (EffSet.is_empty caeffs) -> raise Incorrect_ty
  | _, [] when not (EffSet.is_empty cpeffs) -> raise Incorrect_ty
  | _ ->
    mrg_substs
      [ subst
      ; effs_subst
          (BindMap.of_seq
             (List.to_seq
                (List.map (fun vpeff -> vpeff, caeffs) vpeffs
                @ List.map (fun vaeff -> vaeff, cpeffs) vaeffs)))
      ]
(* match peffs, aeffs with
  | Effs peffs, Effs aeffs when effs_eq aeffs peffs -> subst
  | EffBoundVar pname, EffBoundVar aname when pname = aname -> subst
  | EffVar pname, EffVar aname when pname = aname -> subst
  | EffVar pname, EffVar aname ->
    (match BindMap.find_opt pname subst.effs, BindMap.find_opt aname subst.effs with
    | None, None ->
      mrg_subst
        subst
        (double_effs_subst pname aname (EffVar (safe_tvar_name (pname ^ " " ^ aname))))
    | Some effs, _ -> mrg_subst subst (single_effs_subst aname effs)
    | None, Some effs -> mrg_subst subst (single_effs_subst pname effs))
  | EffVar name, effs | effs, EffVar name -> mrg_subst subst (single_effs_subst name effs)
  | _ -> raise Incorrect_ty *)

and mrg_substs
  =
  (* Format.fprintf
    std_formatter
    "\n%s"
    (Printexc.get_callstack 15 |> Printexc.raw_backtrace_to_string); *)
  function
  | [] -> empty_subst
  | hd :: tl -> mrg_subst (mrg_substs tl) hd

and mrg_subst subst1 subst2 =
  (* Format.fprintf std_formatter "\nsubst1=";
  pp_subst std_formatter subst1;
  Format.fprintf std_formatter "\n";
  Format.fprintf std_formatter "\nsubst2=";
  pp_subst std_formatter subst2;
  Format.fprintf std_formatter "\n"; *)
  let subst =
    BindMap.fold
      (fun name ty subst ->
        match BindMap.find_opt name subst.ty with
        | None -> { ty = BindMap.add name ty subst.ty; effs = subst.effs }
        | Some ty2 ->
          (* Format.fprintf std_formatter "\nty=";
          pp_ty std_formatter ty;
          Format.fprintf std_formatter "\nty2=";
          pp_ty std_formatter ty2;
          Format.fprintf std_formatter "\nsubst=";
          pp_subst std_formatter subst;
          Format.fprintf std_formatter "\n"; *)
          deduce_subst ty ty2 subst)
      subst2.ty
      subst1
  in
  BindMap.fold
    (fun name effs subst ->
      match BindMap.find_opt name subst.effs with
      | None -> { ty = subst.ty; effs = BindMap.add name effs subst.effs }
      | Some effs2 -> deduce_effs_subst effs effs2 subst)
    subst2.effs
    subst
;;

let rec occurs_check name ty subst =
  match ty with
  | TInt | TString | TBool | TExc _ | TBoundVar _ -> ()
  | TTuple l -> List.iter (fun t -> occurs_check name t subst) l
  | TList t | TRef t -> occurs_check name t subst
  | TVar s when s = name -> raise Occurs_fail
  | TVar s ->
    (match BindMap.find_opt s subst.ty with
    | None -> ()
    | Some t -> occurs_check name t subst)
  | TFun (t1, _, t2) ->
    occurs_check name t1 subst;
    occurs_check name t2 subst
;;

let deduce_subst argty effty =
  let subst = deduce_subst argty effty empty_subst in
  BindMap.iter (fun name ty -> occurs_check name ty subst) subst.ty;
  subst
;;

let rec get_effs_subst name subst =
  match BindMap.find_opt name subst.effs with
  | None -> EffSet.singleton (EffVar name)
  | Some effs -> induce_effs_subst effs subst

and induce_effs_subst effs subst =
  EffSet.of_seq
    (Seq.flat_map
       (fun eff ->
         match eff with
         | EffVar name -> EffSet.to_seq (get_effs_subst name subst)
         | _ -> List.to_seq [ eff ])
       (EffSet.to_seq effs))
;;

let rec get_ty_subst name subst =
  match BindMap.find_opt name subst.ty with
  | None -> TVar name
  | Some (TVar name) -> get_ty_subst name subst
  | Some effs -> effs
;;

let rec induce_subst ty subst =
  match ty with
  | TInt | TString | TBool | TExc _ | TBoundVar _ -> ty
  | TTuple l -> TTuple (List.map (fun t -> induce_subst t subst) l)
  | TList t -> TList (induce_subst t subst)
  | TRef t -> TRef (induce_subst t subst)
  | TVar name -> get_ty_subst name subst
  | TFun (ty1, effs, ty2) ->
    TFun (induce_subst ty1 subst, induce_effs_subst effs subst, induce_subst ty2 subst)
;;

let all_effvars effs =
  BindSet.of_list
    (List.filter_map
       (function
         | EffVar name -> Some name
         | _ -> None)
       (List.of_seq (EffSet.to_seq effs)))
;;

let rec all_teffvars = function
  | TInt | TString | TBool | TExc _ | TBoundVar _ -> BindSet.empty, BindSet.empty
  | TTuple l ->
    List.fold_left
      (fun (tys1, effs1) t ->
        let tys2, effs2 = all_teffvars t in
        BindSet.union tys1 tys2, BindSet.union effs1 effs2)
      (BindSet.empty, BindSet.empty)
      l
  | TList t | TRef t -> all_teffvars t
  | TVar name -> BindSet.singleton name, BindSet.empty
  | TFun (ty1, effs, ty2) ->
    let tys1, effs1 = all_teffvars ty1 in
    let tys2, effs2 = all_teffvars ty2 in
    BindSet.union tys1 tys2, BindSet.union (all_effvars effs) (BindSet.union effs1 effs2)
;;

let safe_subst ty =
  let tys, effs = all_teffvars ty in
  { ty =
      BindSet.fold
        (fun name map -> BindMap.add name (TVar (safe_tvar_name name)) map)
        tys
        BindMap.empty
  ; effs =
      BindSet.fold
        (fun name map ->
          BindMap.add name (EffSet.singleton (EffVar (safe_tvar_name name))) map)
        effs
        BindMap.empty
  }
;;

let safe_ty ty = induce_subst ty (safe_subst ty)

let safe_effs =
  EffSet.map (function
      | EffVar name -> EffVar (safe_tvar_name name)
      | effs -> effs)
;;

let safe_tyeffs (ty, effs) = safe_ty ty, safe_effs effs

type chenv =
  { decls : ty_map
  ; btvars : BindSet.t
  ; beffvars : BindSet.t
  }

let bind_effvars env =
  EffSet.map (function
      | EffVar name when is_bound name env.beffvars -> EffBoundVar name
      | effs -> effs)
;;

let rec bind_teffvars env ty =
  match ty with
  | TInt | TString | TBool | TExc _ | TBoundVar _ -> ty
  | TTuple l -> TTuple (List.map (fun t -> bind_teffvars env t) l)
  | TList t -> TList (bind_teffvars env t)
  | TRef t -> TRef (bind_teffvars env t)
  | TVar name -> if is_bound name env.btvars then TBoundVar name else ty
  | TFun (ty1, effs, ty2) ->
    TFun (bind_teffvars env ty1, bind_effvars env effs, bind_teffvars env ty2)
;;

let unbind_effvars env =
  EffSet.map (function
      | EffBoundVar name when is_bound name env.beffvars -> EffVar name
      | effs -> effs)
;;

let rec unbind_teffvars env ty =
  match ty with
  | TInt | TString | TBool | TExc _ | TVar _ -> ty
  | TTuple l -> TTuple (List.map (fun t -> unbind_teffvars env t) l)
  | TList t -> TList (unbind_teffvars env t)
  | TRef t -> TRef (unbind_teffvars env t)
  | TBoundVar name -> if is_bound name env.btvars then TVar name else ty
  | TFun (ty1, effs, ty2) ->
    TFun (unbind_teffvars env ty1, unbind_effvars env effs, unbind_teffvars env ty2)
;;

let simple_subst ty1 ty2 =
  let subst = deduce_subst ty1 ty2 in
  let tvars1, effvars1 = all_teffvars ty1 in
  let tvars2, effvars2 = all_teffvars ty2 in
  let tvars, effvars = BindSet.union tvars1 tvars2, BindSet.union effvars1 effvars2 in
  { ty =
      BindMap.of_seq
        (Seq.map (fun tvar -> tvar, get_ty_subst tvar subst) (BindSet.to_seq tvars))
  ; effs =
      BindMap.of_seq
        (Seq.map
           (fun effvar -> effvar, get_effs_subst effvar subst)
           (BindSet.to_seq effvars))
  }
;;

let mrg_decls decls1 decls2 =
  BindMap.merge
    (fun name ty1 ty2 ->
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
    mrg_decls
      (case_decls (TList ty) ptrn)
      (List.fold_left
         (fun decls p -> mrg_decls decls (case_decls ty p))
         BindMap.empty
         ptrns)
  | _ -> raise Incorrect_ty
;;

let case_env ty ptrn env =
  { decls = BindMap.add_seq (BindMap.to_seq (case_decls ty ptrn)) env.decls
  ; btvars = env.btvars
  ; beffvars = env.beffvars
  }
;;

let check_assignable dty vty env =
  let new_tvars, new_effvars = all_teffvars dty in
  let benv =
    { decls = env.decls
    ; btvars =
        BindSet.of_seq (Seq.append (BindSet.to_seq env.btvars) (BindSet.to_seq new_tvars))
    ; beffvars =
        BindSet.of_seq
          (Seq.append (BindSet.to_seq env.beffvars) (BindSet.to_seq new_effvars))
    }
  in
  (* printf "\nvty=";
  pp_ty std_formatter vty;
  printf "\ndty=";
  pp_ty std_formatter (bind_teffvars benv dty);
  printf "\n";
  pp_ty_map std_formatter env.decls;
  printf "\n\n"; *)
  let _ = deduce_subst vty (bind_teffvars benv dty) in
  ()
;;

let rec infer_tyeffs env expr =
  safe_tyeffs
    (match expr with
    | EConst const ->
      ( (match const with
        | CInt _ -> TInt
        | CString _ -> TString
        | CBool _ -> TBool
        | CEmptyList -> TList (TVar (safe_tvar_name "[]")))
      , EffSet.empty )
    | EVal name -> find_bind env.decls name, EffSet.empty
    | EUnop (op, expr) ->
      let ty, effs = infer_tyeffs env expr in
      (match op, ty with
      | Neg, TInt -> TInt, effs
      | Deref, TRef t -> t, effs
      | _ -> raise Incorrect_ty)
    | EBinop (expr1, op, expr2) ->
      let ty1, effs1 = infer_tyeffs env expr1 in
      let ty2, effs2 = infer_tyeffs env expr2 in
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
      | TRef rty, Asgmt, vty ->
        check_assignable rty vty env;
        TTuple [], EffSet.add EffAsgmt effs
      | ty, Cons, TList lty -> induce_subst (TList lty) (deduce_subst ty lty), effs
      | _ -> raise Incorrect_ty)
    | EApp (f, arg) ->
      let fty, feffs = infer_tyeffs env f in
      let argty, argeffs = infer_tyeffs env arg in
      (match fty with
      | TFun (prmty, effty, retty) ->
        (* printf "\nargty=";
        pp_ty std_formatter argty;
        printf "\nprmty=";
        pp_ty std_formatter prmty;
        printf "\n";
        pp_ty_map std_formatter env.decls;
        printf "\n\n"; *)
        let subst = deduce_subst prmty argty in
        ( induce_subst retty subst
        , EffSet.union (EffSet.union feffs argeffs) (induce_effs_subst effty subst) )
      | _ -> raise Incorrect_ty)
    | ETuple exprs ->
      let tys, effss = List.split (List.map (fun e -> infer_tyeffs env e) exprs) in
      TTuple tys, List.fold_left (fun e1 e2 -> EffSet.union e1 e2) EffSet.empty effss
    | ELet (decl, expr) ->
      let dty = safe_ty (bind_teffvars env decl.ty) in
      let new_env =
        { decls = BindMap.add decl.name dty env.decls
        ; btvars = env.btvars
        ; beffvars = env.beffvars
        }
      in
      let vty, veff = infer_tyeffs (if decl.is_rec then new_env else env) decl.expr in
      (* printf "dty="; pp_ty std_formatter dty; printf "\n";
      printf "vty="; pp_ty std_formatter vty; printf "\n";
      printf "subst="; pp_subst std_formatter (simple_subst vty dty); printf "\n\n"; *)
      check_assignable dty vty env;
      let ty, eff = infer_tyeffs new_env expr in
      ty, EffSet.union veff eff
    (* TODO check pattern type, add decls inside patterns *)
    | EMatch (scr, ptrns) ->
      let scrty, screffs = infer_tyeffs env scr in
      (match ptrns with
      | [] -> raise Empty_macth
      | (ptrn1, case1) :: cases ->
        let ty, effs = infer_tyeffs (case_env scrty ptrn1 env) case1 in
        let ty, effs =
          List.fold_left
            (fun (ty, effs) (ptrn, case) ->
              let ty2, effs2 = infer_tyeffs (case_env scrty ptrn env) case in
              induce_subst ty (deduce_subst ty ty2), EffSet.union effs effs2)
            (ty, EffSet.union screffs effs)
            cases
        in
        ty, effs)
    | EFun (arg, argty, expr) ->
      let argty = bind_teffvars env argty in
      let new_tvars, new_effvars = all_teffvars argty in
      let env =
        { decls = env.decls
        ; btvars =
            BindSet.of_seq
              (Seq.append (BindSet.to_seq env.btvars) (BindSet.to_seq new_tvars))
        ; beffvars =
            BindSet.of_seq
              (Seq.append (BindSet.to_seq env.beffvars) (BindSet.to_seq new_effvars))
        }
      in
      let argty = bind_teffvars env argty in
      let env =
        { decls = BindMap.add arg argty env.decls
        ; btvars = env.btvars
        ; beffvars = env.beffvars
        }
      in
      let resty, effs = infer_tyeffs env expr in
      let unbind_env =
        { decls = BindMap.empty; btvars = new_tvars; beffvars = new_effvars }
      in
      let argty = unbind_teffvars unbind_env argty in
      let resty = unbind_teffvars unbind_env resty in
      let effs = unbind_effvars unbind_env effs in
      TFun (argty, effs, resty), EffSet.empty
    | ETry (scr, excs) ->
      let scrty, screffs = infer_tyeffs env scr in
      let ty, effs =
        List.fold_left
          (fun (ty, effs) (_, case) ->
            let ty2, effs2 = infer_tyeffs env case in
            induce_subst ty (deduce_subst scrty ty2), EffSet.union effs effs2)
          (scrty, EffSet.empty)
          excs
      in
      ( ty
      , EffSet.union
          (EffSet.diff
             screffs
             (EffSet.of_list (List.map (fun (exc, _) -> EffExc exc) excs)))
          effs ))
;;

let stdlib_chenv =
  { decls =
      BindMap.of_seq
        (List.to_seq
           [ "println", TFun (TString, EffSet.singleton EffIO, TTuple [])
           ; "raise1", TFun (TTuple [], EffSet.singleton (EffExc Exc1), TVar "a")
           ; "raise2", TFun (TTuple [], EffSet.singleton (EffExc Exc2), TVar "a")
           ; "ref", TFun (TVar "a", EffSet.empty, TRef (TVar "a"))
           ; ( "sneaky_eff"
             , TFun
                 ( TFun (TVar "a", EffSet.singleton (EffVar "e"), TVar "b")
                 , EffSet.empty
                 , TFun (TVar "a", EffSet.singleton (EffVar "e2"), TVar "b") ) )
           ])
  ; btvars = BindSet.empty
  ; beffvars = BindSet.empty
  }
;;

let check_program =
  List.fold_left
    (fun env (decl : decl) ->
      let dty = safe_ty (bind_teffvars env decl.ty) in
      let new_env =
        { decls = BindMap.add decl.name dty env.decls
        ; btvars = env.btvars
        ; beffvars = env.beffvars
        }
      in
      let vty, _ = infer_tyeffs (if decl.is_rec then new_env else env) decl.expr in
      check_assignable dty vty env;
      new_env)
    stdlib_chenv
;;

(* Tests *)

let test_infer_tyeffs expr matcher =
  let ty, effs = infer_tyeffs stdlib_chenv expr in
  let result = matcher (ty, effs) in
  if result
  then ()
  else (
    printf "Actual:\nty=";
    pp_ty std_formatter ty;
    printf "\neffs=";
    pp_eff_set std_formatter effs;
    printf "\n");
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
