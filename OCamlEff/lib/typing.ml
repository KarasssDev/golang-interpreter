open Ast
open Format

type error =
  | Occurs_check
  | NoVariable of string
  | UnificationFailed of tyexp * tyexp
  | Typing_failure_exp of exp
  | Typing_failure_decl of decl
  | Typing_failure_pat of pat
  | Match_fail of pat * tyexp
  | Binging_error of pat * exp
  | Invalid_Constructor
  | Not_effect_perform
  | Several_bound of pat
  | Multishot_continuation of exp
[@@deriving show { with_path = false }]

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

  (** Creation of a fresh name from internal state *)
  val fresh : int t

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

  let fresh : int t = fun last -> last + 1, Result.Ok last
  let run m = snd (m 0)
end

type fresh = int

let arrow l r = TArrow (l, r)

module VarSet = struct
  include Caml.Set.Make (Int)

  let pp ppf s =
    Format.fprintf ppf "[ ";
    iter (Format.fprintf ppf "%d; ") s;
    Format.fprintf ppf "]"
  ;;

  let fold_R f acc set =
    fold
      (fun x acc ->
        let open R.Syntax in
        let* acc = acc in
        f acc x)
      acc
      set
  ;;
end

type binder_set = VarSet.t [@@deriving show { with_path = false }]
type scheme = S of binder_set * tyexp [@@deriving show { with_path = false }]

module TypeMap = Map.Make (struct
  type t = ident

  let compare = compare
end)

module SubstMap = Map.Make (struct
  type t = fresh

  let compare = compare
end)

module Subst = struct
  type t = tyexp SubstMap.t

  let empty = SubstMap.empty
  let singleton k v = SubstMap.add k v empty
  let find k xs = SubstMap.find k xs
  let remove k xs = SubstMap.remove k xs

  let apply s =
    let rec helper = function
      | TVar x ->
        (match find x s with
        | exception Not_found -> TVar x
        | x -> x)
      | TArrow (l, r) -> TArrow (helper l, helper r)
      | TList x -> TList (helper x)
      | TTuple l -> TTuple (List.map helper l)
      | TEffect x -> TEffect (helper x)
      | other -> other
    in
    helper
  ;;

  let union xs ys = SubstMap.union (fun _ v1 _ -> Some v1) xs ys
  let compose s1 s2 = union (SubstMap.map (apply s1) s2) s1
  let ( ++ ) = compose
  let pp = SubstMap.iter (fun k v -> Printf.printf "[%d -> %s]\n" k (show_tyexp v))
end

module Type = struct
  type t = tyexp

  let rec occurs_in v = function
    | TVar x -> x = v
    | TArrow (l, r) -> occurs_in v l || occurs_in v r
    | TInt | TBool | TString -> false
    | TList tyexp -> occurs_in v tyexp
    | TTuple tyexp_l -> List.exists (occurs_in v) tyexp_l
    | TEffect tyexp -> occurs_in v tyexp
  ;;

  let free_vars =
    let rec helper acc = function
      | TInt | TBool | TString -> acc
      | TVar x -> VarSet.add x acc
      | TArrow (l, r) -> helper (helper acc l) r
      | TList tyexp -> helper acc tyexp
      | TTuple tyexp_l -> List.fold_left helper acc tyexp_l
      | TEffect tyexp -> helper acc tyexp
    in
    helper VarSet.empty
  ;;

  let apply subst t = Subst.apply subst t
end

module Scheme = struct
  type t = scheme

  let occurs_in v = function
    | S (xs, tyexp) -> (not (VarSet.mem v xs)) && Type.occurs_in v tyexp
  ;;

  let free_vars = function
    | S (bs, tyexp) -> VarSet.fold VarSet.remove (Type.free_vars tyexp) bs
  ;;

  let apply sub (S (names, ty)) =
    let s2 = VarSet.fold Subst.remove names sub in
    S (names, Type.apply s2 ty)
  ;;
end

module TypeContext = struct
  type t = scheme TypeMap.t

  let extend context id scheme = TypeMap.add id scheme context
  let empty = TypeMap.empty

  let free_vars typemap =
    TypeMap.fold
      (fun _ v acc -> VarSet.union acc (Scheme.free_vars v))
      typemap
      VarSet.empty
  ;;

  let pp = TypeMap.iter (fun k v -> Printf.printf "%s == %s\n" k (show_scheme v))
  let apply s context = TypeMap.map (Scheme.apply s) context
end

open R
open R.Syntax

let unify l r =
  let rec helper l r =
    match l, r with
    | TInt, TInt | TBool, TBool | TString, TString -> return Subst.empty
    | TList tyexp_1, TList tyexp_2 -> helper tyexp_1 tyexp_2
    | TTuple tyexp_l_1, TTuple tyexp_l_2 ->
      (match tyexp_l_1, tyexp_l_2 with
      | hd1 :: tl1, hd2 :: tl2 ->
        let* subst_hd = helper hd1 hd2 in
        let* subst_tl = helper (TTuple tl1) (TTuple tl2) in
        return (Subst.compose subst_hd subst_tl)
      | [], [] -> return Subst.empty
      | _ -> fail (UnificationFailed (l, r)))
    | TEffect t1, TEffect t2 -> helper t1 t2
    | TVar a, TVar b when a = b -> return Subst.empty
    | TVar b, t when Type.occurs_in b t -> fail Occurs_check
    | t, TVar b when Type.occurs_in b t -> fail Occurs_check
    | TVar b, t | t, TVar b -> return (Subst.singleton b t)
    | TArrow (l1, r1), TArrow (l2, r2) ->
      let* subs1 = helper l1 l2 in
      let* subs2 = helper (Type.apply subs1 r1) (Type.apply subs1 r2) in
      return Subst.(subs2 ++ subs1)
    | _ -> fail (UnificationFailed (l, r))
  in
  helper l r
;;

let instantiate : scheme -> tyexp R.t =
 fun (S (bs, t)) ->
  VarSet.fold_R
    (fun typ name ->
      let* f1 = fresh in
      return @@ Subst.apply (Subst.singleton name (TVar f1)) typ)
    bs
    (return t)
;;

let generalize env ty =
  let free = VarSet.diff (Type.free_vars ty) (TypeContext.free_vars env) in
  S (free, ty)
;;

let lookup_context e xs =
  match TypeMap.find e xs with
  | exception Not_found -> fail (NoVariable e)
  | scheme ->
    let* ans = instantiate scheme in
    return (Subst.empty, ans)
;;

let fresh_var = fresh >>| fun n -> TVar n

let rec contains_pat = function
  | PVar x, PVar y :: _ when x = y -> return true
  | PVar x, PVar y :: tl when x != y -> contains_pat (PVar x, tl)
  | _, _ -> return false
;;

let infer_pat =
  let rec (helper : TypeContext.t -> pat -> (Subst.t * tyexp * TypeContext.t) R.t) =
   fun context -> function
    | PConst x ->
      return
        (match x with
        | CInt _ -> Subst.empty, TInt, context
        | CBool _ -> Subst.empty, TBool, context
        | CString _ -> Subst.empty, TString, context)
    | PCons (pat1, pat2) ->
      let* s1, t1, context1 = helper context pat1 in
      let* s2, t2, context2 = helper context1 pat2 in
      let* s_uni = unify (TList t1) t2 in
      return
        ( Subst.(s_uni ++ s2 ++ s1)
        , TList (Subst.apply Subst.(s_uni ++ s2 ++ s1) t1)
        , TypeMap.union (fun _ _ v2 -> Some v2) context1 context2 )
    | PNil ->
      let* fresh = fresh_var in
      return (Subst.empty, TList fresh, context)
    | PVar x ->
      let* fresh = fresh_var in
      let context2 = TypeContext.extend context x (S (VarSet.empty, fresh)) in
      return (Subst.empty, fresh, context2)
    | PWild ->
      let* fresh = fresh_var in
      return (Subst.empty, fresh, context)
    | PTuple pats ->
      (match pats with
      | hd :: tl ->
        let* sev_bound = contains_pat (hd, tl) in
        if sev_bound
        then fail (Several_bound (PTuple pats))
        else
          let* s1, t1, context1 = helper context hd in
          let* s_tl, t_tl, context2 = helper context1 (PTuple tl) in
          (match t_tl with
          | TTuple tyexps -> return (Subst.(s1 ++ s_tl), TTuple (t1 :: tyexps), context2)
          | _ -> fail (Typing_failure_pat (PTuple pats)))
      | [] -> return (Subst.empty, TTuple [], context))
    | PEffect1 name ->
      let* s, t = lookup_context name context in
      return (s, TEffect t, context)
    | PEffect2 (name, pat) ->
      let* s1, t1 = lookup_context name context in
      let* s2, t2, context1 = helper context pat in
      return (Subst.(s1 ++ s2), TArrow (t1, t2), context1)
    | PEffectH (effpat, k) ->
      let* s1, _, ctx1 = helper context (PVar k) in
      let* s2, _, ctx2 = helper ctx1 effpat in
      let* fresh = fresh_var in
      return (Subst.(s2 ++ s1), fresh, ctx2)
  in
  helper
;;

let return_with_debug ctx exp res =
  let s, t = res in
  let () = TypeContext.pp ctx in
  let () = Subst.pp s in
  let () = Printf.printf "Expression: %s\n" (show_exp exp) in
  let () = Printf.printf "Type: %s\n\n" (show_tyexp t) in
  return res
;;

let rec cont_cnt = function
  | ENil | EConst _ | EVar _ | EEffect1 _ -> 0
  | EOp (_, exp1, exp2) | ECons (exp1, exp2) -> cont_cnt exp1 + cont_cnt exp2
  | EUnOp (_, exp) | EFun (_, exp) | EApp (_, exp) | EPerform exp | EEffect2 (_, exp) ->
    cont_cnt exp
  | ETuple exps -> List.fold_left (fun acc exp -> acc + cont_cnt exp) 0 exps
  | EIf (exp1, exp2, exp3) -> cont_cnt exp1 + cont_cnt exp2 + cont_cnt exp3
  | ELet (bindings, exp) ->
    cont_cnt exp + List.fold_left (fun acc (_, _, exp) -> acc + cont_cnt exp) 0 bindings
  | EMatch (exp, cases) ->
    cont_cnt exp + List.fold_left (fun acc (_, exp) -> acc + cont_cnt exp) 0 cases
  | EContinue (_, exp) -> 1 + cont_cnt exp
;;

let rec match_pat context = function
  | PVar p, exp ->
    let* s1, t1 = infer_exp context exp in
    let context2 = TypeContext.apply s1 context in
    let t2 = generalize context2 t1 in
    return (s1, TypeContext.extend context2 p t2)
  | PTuple (hd_p :: tl_p), ETuple (hd_e :: tl_e) ->
    let* oc_check = contains_pat (hd_p, tl_p) in
    if oc_check
    then fail Occurs_check
    else
      let* s1, context1 = match_pat context (hd_p, hd_e) in
      let* s2, context2 = match_pat context (PTuple tl_p, ETuple tl_e) in
      let context_uni = TypeMap.union (fun _ v1 _ -> Some v1) context1 context2 in
      return (Subst.(s2 ++ s1), context_uni)
  | PTuple [], ETuple [] -> return (Subst.empty, context)
  | PWild, exp ->
    let* s1, _ = infer_exp context exp in
    let context2 = TypeContext.apply s1 context in
    return (s1, context2)
  | a, b -> fail (Binging_error (a, b))

and infer_exp context = function
  | EConst x ->
    return
      (match x with
      | CInt _ -> Subst.empty, TInt
      | CBool _ -> Subst.empty, TBool
      | CString _ -> Subst.empty, TString)
  | EOp (op, exp1, exp2) ->
    (*  
          Эмуляция аппликации двух выражений к tyexp1 -> tyexp2 -> tyexp3.
          После проблем с выводом типов выражений слева и справа в бин операции,
          было решено сделать вот так, чтобы оно просто работало.
       *)
    let mega_helper tyexp1 tyexp2 tyexp3 =
      let* tv1 = fresh_var in
      let t1 = TArrow (tyexp1, TArrow (tyexp2, tyexp3)) in
      let* s2, t2 = infer_exp context exp1 in
      let* s3 = unify (Subst.apply s2 t1) (TArrow (t2, tv1)) in
      let trez1 = Subst.apply s3 tv1 in
      let s4 = Subst.(s3 ++ s2) in
      let* tv2 = fresh_var in
      let* s5, t3 = infer_exp (TypeContext.apply s4 context) exp2 in
      let* s6 = unify (Subst.apply s5 trez1) (TArrow (t3, tv2)) in
      let trez2 = Subst.apply s6 tv2 in
      let s7 = Subst.(s6 ++ s5 ++ s4) in
      return (s7, trez2)
    in
    (match op with
    | Add | Sub | Mul | Div -> mega_helper TInt TInt TInt
    | And | Or -> mega_helper TBool TBool TBool
    | _ ->
      let* tv0 = fresh_var in
      mega_helper tv0 tv0 TBool)
  | EUnOp (op, exp) ->
    let* s, t = infer_exp context exp in
    (match op with
    | Minus ->
      let* s_int = unify t TInt in
      return (Subst.(s_int ++ s), TInt)
    | Not ->
      let* s_bool = unify t TBool in
      return (Subst.(s_bool ++ s), TBool))
  | EVar x -> lookup_context x context
  | ETuple exps ->
    (match exps with
    | hd :: tl ->
      let* s1, t1 = infer_exp context hd in
      let* s_tl, t_tl = infer_exp context (ETuple tl) in
      (match t_tl with
      | TTuple tyexps -> return (Subst.(s1 ++ s_tl), TTuple (t1 :: tyexps))
      | _ -> fail (Typing_failure_exp (ETuple exps)))
    | [] -> return (Subst.empty, TTuple []))
  | ENil ->
    let* fresh = fresh_var in
    return (Subst.empty, TList fresh)
  | ECons (exp1, exp2) ->
    let* s1, t1 = infer_exp context exp1 in
    let* s2, t2 = infer_exp context exp2 in
    (match t2 with
    | TList _ ->
      let* s_uni = unify (TList t1) t2 in
      return (Subst.(s1 ++ s2 ++ s_uni), TList (Subst.apply s_uni t1))
    | TVar _ -> return (Subst.(s1 ++ s2), TList (Subst.apply s2 t1))
    | _ -> fail (Typing_failure_exp (ECons (exp1, exp2))))
  | EIf (exp1, exp2, exp3) ->
    let* s1, t1 = infer_exp context exp1 in
    let* s2, t2 = infer_exp context exp2 in
    let* s3, t3 = infer_exp context exp3 in
    let* s4 = unify t1 TBool in
    let* s5 = unify t2 t3 in
    return (Subst.(s5 ++ s4 ++ s3 ++ s2 ++ s1), Subst.apply s5 t2)
  | ELet (bindings, in_exp) ->
    (match bindings with
    | hd :: tl ->
      (match hd with
      | false, pat, exp ->
        let* s1, context2 = match_pat context (pat, exp) in
        let* s2, t3 = infer_exp context2 (ELet (tl, in_exp)) in
        return (Subst.(s1 ++ s2), t3)
      | true, PVar x, exp ->
        let* fresh = fresh_var in
        let context = TypeContext.extend context x (S (VarSet.empty, fresh)) in
        let* s1, t1 = infer_exp context exp in
        let* s2 = unify (Subst.apply s1 fresh) t1 in
        let s = Subst.(s2 ++ s1) in
        let context2 = TypeContext.apply s context in
        let t2 = generalize context2 (Subst.apply s fresh) in
        infer_exp TypeContext.(extend (apply s context2) x t2) (ELet (tl, in_exp))
      | _ -> fail (Typing_failure_exp (ELet (bindings, in_exp))))
    | [] ->
      let* s, t = infer_exp context in_exp in
      return (s, t))
  | EFun (pat, exp) ->
    let* s1, t1, context1 = infer_pat context pat in
    let* s2, t2 = infer_exp context1 exp in
    let s = Subst.(s1 ++ s2) in
    let trez = TArrow (Subst.apply s2 t1, t2) in
    return (s, trez)
  | EApp (exp1, exp2) ->
    let* s1, t1 = infer_exp context exp1 in
    let* s2, t2 = infer_exp (TypeContext.apply s1 context) exp2 in
    let* tv = fresh_var in
    let* s3 = unify (Subst.apply s2 t1) (TArrow (t2, tv)) in
    let trez = Subst.apply s3 tv in
    return (Subst.(s3 ++ s2 ++ s1), trez)
  | EMatch (exp_main, cases) ->
    let* s0, t0 = infer_exp context exp_main in
    let rec mega_helper = function
      | [ (_, exp1) ] when cont_cnt exp1 > 1 -> fail (Multishot_continuation exp1)
      | [ (pat, exp) ] ->
        let* s1, t1, context1 = infer_pat context pat in
        let* s2 = unify t0 t1 in
        let* s3, t3 = infer_exp context1 exp in
        let s = Subst.(s3 ++ s2 ++ s1 ++ s0) in
        return (s, Subst.apply s t3)
      | (_, exp1) :: (_, _) :: _ when cont_cnt exp1 > 1 ->
        fail (Multishot_continuation exp1)
      | (pat1, exp1) :: (pat2, exp2) :: tl ->
        let* s1, t1, context1 = infer_pat context pat1 in
        let* s2, t2, context2 = infer_pat context pat2 in
        let* s3 = unify t0 t1 in
        let* s4 = unify t0 t2 in
        let* s44 = unify t1 t2 in
        let* s5, t5 = infer_exp context1 exp1 in
        let* s6, t6 = infer_exp context2 exp2 in
        let* s7 = unify t5 t6 in
        let* s8, t8 = mega_helper ((pat2, exp2) :: tl) in
        let* s9 = unify t6 t8 in
        let s = Subst.(s9 ++ s8 ++ s7 ++ s6 ++ s5 ++ s44 ++ s4 ++ s3 ++ s2 ++ s1) in
        return (s, Subst.apply s t8)
      | [] -> fail (Typing_failure_exp (EMatch (exp_main, cases)))
    in
    let* s, t = mega_helper cases in
    return (s, Subst.apply s t)
  | EEffect1 id -> lookup_context id context
  | EEffect2 (id, exp) ->
    let* _, effty = lookup_context id context in
    (match effty with
    | TArrow (a, b) ->
      let* s1, tyexp = infer_exp context exp in
      let* s2 = unify a tyexp in
      return (Subst.(s2 ++ s1), b)
    | _ -> fail Invalid_Constructor)
  | EPerform exp ->
    let* s1, tyexp = infer_exp context exp in
    (match tyexp with
    | TEffect t -> return (s1, t)
    | t ->
      let* tv = fresh_var in
      let* s = unify t (TEffect tv) in
      return (s, tv))
  | EContinue (k, _) ->
    let* _ = lookup_context k context in
    let* tv = fresh_var in
    return (Subst.empty, tv)
;;

let infer_decl context = function
  | DLet binding ->
    (match binding with
    | false, pat, exp ->
      let* _, context1 = match_pat context (pat, exp) in
      return context1
    | true, PVar x, exp ->
      let* fresh = fresh_var in
      let context = TypeContext.extend context x (S (VarSet.empty, fresh)) in
      let* s1, t1 = infer_exp context exp in
      let* s2 = unify (Subst.apply s1 fresh) t1 in
      let s = Subst.(s2 ++ s1) in
      let context2 = TypeContext.apply s context in
      let t2 = generalize context2 (Subst.apply s fresh) in
      return (TypeContext.extend context2 x t2)
    | _ -> fail (Typing_failure_decl (DLet binding)))
  | DEffect1 (id, ty) ->
    return @@ TypeContext.extend context id (S (VarSet.empty, TEffect ty))
  | DEffect2 (id, ty1, ty2) ->
    return @@ TypeContext.extend context id (S (VarSet.empty, TArrow (ty1, TEffect ty2)))
;;

let infer_prog prog =
  let context_empty = return TypeContext.empty in
  let ctx =
    List.fold_left
      (fun context decl ->
        let* context = context in
        infer_decl context decl)
      context_empty
      prog
  in
  match R.run ctx with
  | Ok _ -> true
  | Error x ->
    pp_error std_formatter x;
    false
;;
