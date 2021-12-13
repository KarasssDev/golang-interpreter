open Ast
open Format
open Printexc
module BindMap = Map.Make (String)
module BindSet = Set.Make (String)

type ty_map = ty BindMap.t
type effs_map = eff_set BindMap.t

exception Incorrect_ty
exception Rec_subst
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
  | TInt, TInt | TString, TString | TBool, TBool -> subst
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

let rec check_non_rec name ty subst =
  match ty with
  | TInt | TString | TBool | TExc _ | TBoundVar _ -> ()
  | TTuple l -> List.iter (fun t -> check_non_rec name t subst) l
  | TList t | TRef t -> check_non_rec name t subst
  | TVar s when s = name -> raise Rec_subst
  | TVar s ->
    (match BindMap.find_opt s subst.ty with
    | None -> ()
    | Some t -> check_non_rec name t subst)
  | TFun (t1, _, t2) ->
    check_non_rec name t1 subst;
    check_non_rec name t2 subst
;;

let deduce_subst argty effty =
  let subst = deduce_subst argty effty empty_subst in
  BindMap.iter (fun name ty -> check_non_rec name ty subst) subst.ty;
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
  printf "\nvty=";
  pp_ty std_formatter vty;
  printf "\ndty=";
  pp_ty std_formatter (bind_teffvars benv dty);
  printf "\n";
  pp_ty_map std_formatter env.decls;
  printf "\n\n";
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
      | TInt, Geq, TInt -> TBool, effs
      | TString, Eq, TString | TString, Neq, TString -> TBool, effs
      | TBool, Eq, TBool | TBool, Neq, TBool | TBool, And, TBool | TBool, Or, TBool ->
        TBool, effs
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
        printf "\nargty=";
        pp_ty std_formatter argty;
        printf "\nprmty=";
        pp_ty std_formatter prmty;
        printf "\n";
        pp_ty_map std_formatter env.decls;
        printf "\n\n";
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
      new_env
  )
  {
    decls = BindMap.empty;
    btvars = BindSet.empty;
    beffvars = BindSet.empty
  }

(* open Ast
module BindMap = Map.Make (String)
module BindSet = Set.Make (String)

let eff_subset effs1 effs2 =
  List.for_all
    (fun eff1 ->
      match List.find_opt (fun eff2 -> equal_eff eff1 eff2) effs2 with
      | Some _ -> true
      | None -> false)
    effs1
;;

(* TODO *)
let is_subty subty superty = true

exception Incorrect_ty

let check_subty subty superty = if is_subty subty superty then () else raise Incorrect_ty

exception Not_bound

let find_bind map name =
  try BindMap.find name map with
  | Not_found -> raise Not_bound
;;

let is_bound set name =
  try
    let _ = BindSet.find set name in
    true
  with
  | Not_found -> false
;;

type bind_set = BindSet.t
type ty_map = ty BindMap.t
type eff_map = eff list BindMap.t

type chenv =
  { decls : ty_map
  ; btvars : BindSet.t
  ; beffvars : BindSet.t
  }

let safe_tvar_name name = name ^ ":" ^ string_of_int (Random.bits ())
(* ^ string_of_int (Random.bits ())
  ^ string_of_int (Random.bits ())
  ^ string_of_int (Random.bits ())
  ^ string_of_int (Random.bits ()) *)

type tvar_grp =
  { names : bind_set
  ; ty : ty
  }

let tvar_grp_singleton name ty = { names = BindSet.singleton name; ty }

let x = BindMap.fold

type tvar_grp_map = tvar_grp BindMap.t

let mrg_tvar_grps g1 g2 =
  { names = BindSet.union g1.names g2.names
  ; ty =
      (match g2.ty with
      | TVar _ -> g1.ty
      | ty2 ->
        (match g1.ty with
        | TVar _ -> g2.ty
        (* TODO smart recursive ty merge instead of eff_eq (return multiple resulting groups) and use context so that ('a, int) and (int, int) can be merged if 'a isn't yet bound *)
        | ty1 when equal_ty ty1 ty2 -> ty1
        | _ -> raise Incorrect_ty))
  }
;;

let pp_tvar_grp_map fmt map =
  BindMap.fold
    (fun k v _ ->
      Format.fprintf fmt "%s=" k;
      pp_ty fmt v.ty;
      Format.fprintf fmt "\n")
    map
    ()
;;

let pp_eff_map fmt map =
  BindMap.fold
    (fun k v _ ->
      Format.fprintf fmt "%s=" k;
      List.iter
        (fun e ->
          pp_eff fmt e;
          Format.fprintf fmt ",")
        v;
      Format.fprintf fmt "\n")
    map
    ()
;;

(* Deduction (rename to substition) *)
type deduc =
  { ty : tvar_grp_map
  ; eff : eff_map
  }
[@@deriving show { with_path = false }]

let empty_deduc = { ty = BindMap.empty; eff = BindMap.empty }
let ty_deduc ty = { ty; eff = BindMap.empty }

let ty_deduc_grp grp =
  ty_deduc
    (BindSet.fold (fun name map -> BindMap.add name grp map) grp.names BindMap.empty)
;;

let ty_deduc_singleton name ty = ty_deduc_grp (tvar_grp_singleton name ty)
let eff_deduc eff = { ty = BindMap.empty; eff }

let mrg_tys ty1 ty2 subst = 
  match ty1 with
  | TVar name1 -> (match (BindMap.find_opt name1 subst.ty) with 
      | None -> BindMap. )
  | _ -> failwith ""

let mrg_deducs d1 d2 =
  { ty =
      BindMap.fold
        (fun name group1 tvars ->
          match BindMap.find_opt name tvars with
          | None -> BindMap.add name group1 tvars
          | Some group2 ->
            let group = mrg_tvar_grps group1 group2 in
            BindSet.fold
              (fun name tvars -> BindMap.add name group tvars)
              group.names
              tvars)
        d2.ty
        d1.ty
  ; eff =
      BindMap.merge
        (fun _ eff1_opt eff2_opt ->
          match eff1_opt, eff2_opt with
          | Some e1, Some e2 ->
            if eff_subset e1 e2 && eff_subset e2 e1 then Some e1 else raise Incorrect_ty
          | None, x -> x
          | x, None -> x)
        d1.eff
        d2.eff
  }
;;

(* let merge_deductions d1 d2 =
  
  ( BindMap.merge
      (fun name ty1_opt ty2_opt ->
        match ty1_opt, ty2_opt with
        (* TODO if types t1 != t2 && name.startsWith("arg ") && (
          t1 is TVar(name) && (ty[name] == t2 || ty.CAS(null, t2)) ||
          t2 is TVar(name) && (ty[name] == t1 || ty.CAS(null, t1)) ||
          t1 is TVar(name1) && t2 is TVar(name2) &&...
          )
        *)
        (* TODO if types aren't equal and one match TVar("arg " ^ name) maybe TVar is bound to matching type
          or TVar isn't yet bound and can be bound to a matching type *)
        | Some t1, Some t2 -> if equal_ty t1 t2 then Some t1 else raise Incorrect_ty
        | None, x -> x
        | x, None -> x)
      ty1
      ty2
  , BindMap.merge
      (fun _ eff1_opt eff2_opt ->
        match eff1_opt, eff2_opt with
        | Some e1, Some e2 ->
          (* TODO allow permuations *)
          if List.equal equal_eff e1 e2 then Some e1 else raise Incorrect_ty
        | None, x -> x
        | x, None -> x)
      eff1
      eff2 )
;; *)

let rec deduce_tvars prmty argty covar =
  match argty with
  | TVar argname ->
    (match prmty with
    | TVar prmname ->
      ty_deduc_grp
        { names = BindSet.of_list [ argname; prmname ]
        ; ty = TVar (safe_tvar_name (argname ^ " " ^ prmname))
        }
    | _ -> ty_deduc_singleton argname prmty)
  | _ ->
    (match prmty with
    | TInt ->
      (match argty with
      | TInt -> empty_deduc
      | _ -> raise Incorrect_ty)
    | TString ->
      (match argty with
      | TString -> empty_deduc
      | _ -> raise Incorrect_ty)
    | TBool ->
      (match argty with
      | TBool -> empty_deduc
      | _ -> raise Incorrect_ty)
    | TExc prm_exc ->
      (match argty with
      | TExc arg_exc when equal_exc prm_exc arg_exc -> empty_deduc
      | _ -> raise Incorrect_ty)
    | TBoundVar name ->
      (match argty with
      | TBoundVar name2 when name = name2 -> empty_deduc
      | _ -> raise Incorrect_ty)
    | TTuple prmtys ->
      (match argty with
      | TTuple argtys ->
        List.fold_right
          (fun d1 d2 -> mrg_deducs d1 d2)
          (List.map (fun (p, a) -> deduce_tvars p a covar) (List.combine prmtys argtys))
          empty_deduc
      | _ -> raise Incorrect_ty)
    | TList prmty ->
      (match argty with
      | TList argty -> deduce_tvars prmty argty covar
      | _ -> raise Incorrect_ty)
    | TRef prmty ->
      (match argty with
      | TRef argty -> deduce_tvars prmty argty covar
      | _ -> raise Incorrect_ty)
    | TVar name -> ty_deduc_singleton name argty
    | TFun (p1, peff, p2) ->
      (match argty with
      | TFun (a1, aeff, a2) ->
        mrg_deducs
          (mrg_deducs (deduce_tvars p1 a1 (not covar)) (deduce_tvars p2 a2 covar))
          (match
             List.find_opt
               (fun eff ->
                 match eff with
                 | EffVar _ -> true
                 | _ -> false)
               peff
           with
          | Some _ ->
            eff_deduc
              (List.fold_right
                 (fun eff map ->
                   match eff with
                   | EffVar s -> BindMap.add s aeff map
                   | _ -> map)
                 peff
                 BindMap.empty)
          | None when if covar then eff_subset aeff peff else eff_subset peff aeff ->
            empty_deduc
          | _ -> raise Incorrect_ty)
      | _ -> raise Incorrect_ty))
;;

let deduce_tvars prmty argty = deduce_tvars prmty argty true

let apply_eff_deduc effs deduc =
  List.flatten
    (List.map
       (fun eff ->
         match eff with
         | EffVar name -> Option.value ~default:[ eff ] (BindMap.find_opt name deduc.eff)
         | _ -> [ eff ])
       effs)
;;

(* rename induce *)
let rec apply_deduc ty deduc =
  match ty with
  | TInt | TString | TBool | TExc _ | TBoundVar _ -> ty
  | TTuple l -> TTuple (List.map (fun t -> apply_deduc t deduc) l)
  | TList t -> TList (apply_deduc t deduc)
  | TRef t -> TRef (apply_deduc t deduc)
  | TVar name ->
    (match BindMap.find_opt name deduc.ty with
    | Some grp -> grp.ty
    | None -> ty)
  | TFun (ty1, effs, ty2) ->
    TFun (apply_deduc ty1 deduc, apply_eff_deduc effs deduc, apply_deduc ty2 deduc)
;;

let all_evars effs =
  BindSet.of_list
    (List.filter_map
       (fun eff ->
         match eff with
         | EffVar name -> Some name
         | _ -> None)
       effs)
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
  | TList t -> all_teffvars t
  | TRef t -> all_teffvars t
  | TVar name -> BindSet.singleton name, BindSet.empty
  | TFun (ty1, effs, ty2) ->
    let tys1, effs1 = all_teffvars ty1 in
    let tys2, effs2 = all_teffvars ty2 in
    BindSet.union tys1 tys2, BindSet.union (all_evars effs) (BindSet.union effs1 effs2)
;;

let safe_deduc ty =
  let tys, effs = all_teffvars ty in
  { ty =
      BindSet.fold
        (fun name map ->
          BindMap.add name (tvar_grp_singleton name (TVar (safe_tvar_name name))) map)
        tys
        BindMap.empty
  ; eff =
      BindSet.fold
        (fun name map -> BindMap.add name [ EffVar (safe_tvar_name name) ] map)
        effs
        BindMap.empty
  }
;;

let safe_ty ty = apply_deduc ty (safe_deduc ty)

let safe_effs effs =
  List.map
    (fun eff ->
      match eff with
      | EffVar name -> EffVar (safe_tvar_name name)
      | _ -> eff)
    effs
;;

let safe_tyeffs (ty, effs) = safe_ty ty, safe_effs effs

let bind_effvars env effs =
  List.map (fun eff -> match eff with
  | EffVar name -> if is_bound name env.beffvars then EffBoundVar(name) else eff
  | _ -> eff) effs

let rec bind_teffvars env ty =
  match ty with
  | TInt | TString | TBool | TExc _ | TBoundVar _ -> ty
  | TTuple l -> TTuple (List.map (fun t -> bind_teffvars env t) l)
  | TList t -> TList (bind_teffvars env t)
  | TRef t -> TRef (bind_teffvars env t)
  | TVar name ->
    if is_bound name env.btvars then TBoundVar(name) else ty
  | TFun (ty1, effs, ty2) ->
    TFun (bind_teffvars env ty1, bind_effvars env effs, bind_teffvars env ty2)
;;

let unbind_effvars env effs =
  List.map (fun eff -> match eff with
  | EffBoundVar name -> if is_bound name env.beffvars then EffVar(name) else eff
  | _ -> eff) effs

let rec unbind_teffvars env ty =
  match ty with
  | TInt | TString | TBool | TExc _ | TVar _ -> ty
  | TTuple l -> TTuple (List.map (fun t -> unbind_teffvars env t) l)
  | TList t -> TList (unbind_teffvars env t)
  | TRef t -> TRef (unbind_teffvars env t)
  | TBoundVar name ->
    if is_bound name env.btvars then TVar(name) else ty
  | TFun (ty1, effs, ty2) ->
    TFun (unbind_teffvars env ty1, unbind_effvars env effs, unbind_teffvars env ty2)
;;

(* TODO use Random.int64 twice to rename generics right after obtaining any value that has not bound TVars *)
let rec infer_tyeffs env expr =
  safe_tyeffs
    (match expr with
    | EConst const ->
      ( (match const with
        | CInt _ -> TInt
        | CString _ -> TString
        | CBool _ -> TBool
        | CEmptyList -> TList (TVar (safe_tvar_name "[]")))
      , [] )
    | EVal name -> find_bind env.decls name, []
    | EApp (f, arg) ->
      let fty, feffs = infer_tyeffs env f in
      let argty, argeffs = infer_tyeffs env arg in
      (match fty with
      | TFun (prmty, effty, retty) ->
        let deduc = deduce_tvars prmty argty in
        apply_deduc retty deduc, feffs @ argeffs @ apply_eff_deduc effty deduc
      | _ -> raise Incorrect_ty)
    | ELet (decl, expr) ->
      let vty, veff = infer_tyeffs env decl.expr in
      let dty = safe_ty (bind_teffvars env decl.ty) in
      let _ = deduce_tvars vty dty in
      let ty, eff = infer_tyeffs ({
         decls = BindMap.add (decl.name) dty env.decls;
         btvars = env.btvars;
         beffvars = env.beffvars;
         }) expr in
      ty, veff @ eff
    | EFun (arg, argty, expr) ->
      let argty = bind_teffvars env argty in
      let (new_tvars, new_effvars) = all_teffvars argty in
      let env = {
        decls = env.decls;
        btvars = BindSet.of_seq (Seq.append (BindSet.to_seq env.btvars) (BindSet.to_seq new_tvars));
        beffvars = BindSet.of_seq (Seq.append (BindSet.to_seq env.beffvars) (BindSet.to_seq new_effvars));
      } in
      let argty = bind_teffvars env argty in
      let env = {
        decls = BindMap.add arg argty env.decls;
        btvars = env.btvars;
        beffvars = env.beffvars; 
      } in
      let (resty, effs) = infer_tyeffs env expr in
      let unbind_env = { decls = BindMap.empty; btvars = new_tvars; beffvars = new_effvars; } in
      let argty = unbind_teffvars unbind_env argty in
      let resty = unbind_teffvars unbind_env resty in
      let effs = unbind_effvars unbind_env effs in
      TFun(argty, effs, resty), []
    | _ -> TInt, [])
;; *)
