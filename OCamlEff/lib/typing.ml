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
  | Not_Implemented (* to be removed *)
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

(**   я здесь   *)
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
      let* s2, t2, context2 = helper context pat2 in
      (match t2 with
      | TList _ ->
        let* s_uni = unify (TList t1) t2 in
        return
          ( Subst.(s_uni ++ s1 ++ s2)
          , TList (Subst.apply Subst.(s_uni ++ s2 ++ s1) t1)
          , TypeMap.union (fun _ _ v2 -> Some v2) context1 context2 )
      | TVar _ ->
        let* s_uni = unify (TList t1) t2 in
        return
          ( Subst.(s_uni ++ s1 ++ s2)
          , TList (Subst.apply Subst.(s_uni ++ s2 ++ s1) t1)
          , TypeMap.union (fun _ _ v2 -> Some v2) context1 context2 )
      | _ -> fail (Typing_failure_pat (PCons (pat1, pat2))))
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
        let* oc_check = contains_pat (hd, tl) in
        if oc_check
        then fail Occurs_check
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
    | PEffectH (_, _) ->
      let* fresh = fresh_var in
      return (Subst.empty, fresh, context)
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

let infer_exp =
  let rec helper context expr =
    match expr with
    | EConst x ->
      return_with_debug
        context
        expr
        (match x with
        | CInt _ -> Subst.empty, TInt
        | CBool _ -> Subst.empty, TBool
        | CString _ -> Subst.empty, TString)
    | EOp (op, exp1, exp2) ->
      (match op with
      | Add | Sub | Mul | Div ->
        let* tv1 = fresh_var in
        let t1 = TArrow (TInt, TArrow (TInt, TInt)) in
        let* s2, t2 = helper context exp1 in
        let* s3 = unify (Subst.apply s2 t1) (TArrow (t2, tv1)) in
        let trez1 = Subst.apply s3 tv1 in
        let s4 = Subst.(s3 ++ s2) in
        let* tv2 = fresh_var in
        let* s5, t3 = helper (TypeContext.apply s4 context) exp2 in
        let* s6 = unify (Subst.apply s5 trez1) (TArrow (t3, tv2)) in
        let trez2 = Subst.apply s6 tv2 in
        let s7 = Subst.(s6 ++ s5 ++ s4) in
        return_with_debug context expr (s7, trez2)
      | And | Or ->
        let* tv1 = fresh_var in
        let t1 = TArrow (TBool, TArrow (TBool, TBool)) in
        let* s2, t2 = helper context exp1 in
        let* s3 = unify (Subst.apply s2 t1) (TArrow (t2, tv1)) in
        let trez1 = Subst.apply s3 tv1 in
        let s4 = Subst.(s3 ++ s2) in
        let* tv2 = fresh_var in
        let* s5, t3 = helper (TypeContext.apply s4 context) exp2 in
        let* s6 = unify (Subst.apply s5 trez1) (TArrow (t3, tv2)) in
        let trez2 = Subst.apply s6 tv2 in
        let s7 = Subst.(s6 ++ s5 ++ s4) in
        return_with_debug context expr (s7, trez2)
      | _ ->
        let* tv0 = fresh_var in
        let* tv1 = fresh_var in
        let t1 = TArrow (tv0, TArrow (tv0, TBool)) in
        let* s2, t2 = helper context exp1 in
        let* s3 = unify (Subst.apply s2 t1) (TArrow (t2, tv1)) in
        let trez1 = Subst.apply s3 tv1 in
        let s4 = Subst.(s3 ++ s2) in
        let* tv2 = fresh_var in
        let* s5, t3 = helper (TypeContext.apply s4 context) exp2 in
        let* s6 = unify (Subst.apply s5 trez1) (TArrow (t3, tv2)) in
        let trez2 = Subst.apply s6 tv2 in
        let s7 = Subst.(s6 ++ s5 ++ s4) in
        return_with_debug context expr (s7, trez2))
    | EUnOp (op, exp) ->
      let* s, t = helper context exp in
      (match op with
      | Minus ->
        let* s_int = unify t TInt in
        return_with_debug context expr (Subst.(s_int ++ s), TInt)
      | Not ->
        let* s_bool = unify t TBool in
        return_with_debug context expr (Subst.(s_bool ++ s), TBool))
    | EVar x -> lookup_context x context
    | ETuple exps ->
      (match exps with
      | hd :: tl ->
        let* s1, t1 = helper context hd in
        let* s_tl, t_tl = helper context (ETuple tl) in
        (match t_tl with
        | TTuple tyexps ->
          return_with_debug context expr (Subst.(s1 ++ s_tl), TTuple (t1 :: tyexps))
        | _ -> fail (Typing_failure_exp (ETuple exps)))
      | [] -> return_with_debug context expr (Subst.empty, TTuple []))
    | ENil ->
      let* fresh = fresh_var in
      return_with_debug context expr (Subst.empty, TList fresh)
    | ECons (exp1, exp2) ->
      let* s1, t1 = helper context exp1 in
      let* s2, t2 = helper context exp2 in
      (match t2 with
      | TList _ ->
        let* s_uni = unify (TList t1) t2 in
        return_with_debug
          context
          expr
          (Subst.(s1 ++ s2 ++ s_uni), TList (Subst.apply s_uni t1))
      | TVar _ ->
        let* s_uni = unify (TList t1) t2 in
        return_with_debug
          context
          expr
          (Subst.(s1 ++ s2 ++ s_uni), TList (Subst.apply s_uni t1))
      | _ -> fail (Typing_failure_exp (ECons (exp1, exp2))))
    | EIf (exp1, exp2, exp3) ->
      let* s1, t1 = helper context exp1 in
      let* s2, t2 = helper context exp2 in
      let* s3, t3 = helper context exp3 in
      let* s4 = unify t1 TBool in
      let* s5 = unify t2 t3 in
      return_with_debug
        context
        expr
        (Subst.(s5 ++ s4 ++ s3 ++ s2 ++ s1), Subst.apply s5 t2)
    | ELet (bindings, in_exp) ->
      (match bindings with
      | hd :: tl ->
        (match hd with
        | false, PVar x, exp ->
          let* s1, t1 = helper context exp in
          let context2 = TypeContext.apply s1 context in
          let t2 = generalize context2 t1 in
          let* s2, t3 = helper (TypeContext.extend context2 x t2) (ELet (tl, in_exp)) in
          return_with_debug context expr (Subst.(s1 ++ s2), t3)
        | true, PVar x, exp ->
          let* fresh = fresh_var in
          let context = TypeContext.extend context x (S (VarSet.empty, fresh)) in
          let* s1, t1 = helper context exp in
          let* _ = unify fresh t1 in
          let context2 = TypeContext.apply s1 context in
          let t2 = generalize context2 t1 in
          let* s2, t3 = helper (TypeContext.extend context2 x t2) (ELet (tl, in_exp)) in
          return_with_debug context expr (Subst.(s1 ++ s2), t3)
        | _ -> fail (Typing_failure_exp (ELet (bindings, in_exp))))
      | [] ->
        let* s, t = helper context in_exp in
        return_with_debug context expr (s, t))
    | EFun (pat, exp) ->
      let* s1, t1, context1 = infer_pat context pat in
      let* s2, t2 = helper context1 exp in
      let s = Subst.(s1 ++ s2) in
      let trez = TArrow (Subst.apply s2 t1, t2) in
      return_with_debug context expr (s, trez)
    | EApp (exp1, exp2) ->
      let* tv = fresh_var in
      let* s1, t1 = helper context exp1 in
      let* s2, t2 = helper (TypeContext.apply s1 context) exp2 in
      let* s3 = unify (Subst.apply s2 t1) (TArrow (t2, tv)) in
      let trez = Subst.apply Subst.(s3 ++ s2) tv in
      return_with_debug context expr (Subst.(s3 ++ s2 ++ s1), trez)
    | EMatch (exp_main, cases) ->
      let* s0, t0 = helper context exp_main in
      let l =
        List.map
          (fun (pat, exp) ->
            let* s1, t1, context1 = infer_pat context pat in
            match R.run (unify t0 t1) with
            | Ok x ->
              let* s2, t2 = helper context1 exp in
              return (Subst.(x ++ s1), s2, Subst.apply Subst.(x ++ s1) t2)
            | Error _ -> fail (Typing_failure_exp (EMatch (exp_main, cases))))
          cases
      in
      let rec mega_helper = function
        | s0, hd1 :: hd2 :: tl ->
          let* s01, s1, l1 = hd1 in
          let* s02, s2, l2 = hd2 in
          (match R.run (unify (Subst.apply s0 l1) (Subst.apply s0 l2)) with
          | Ok x -> mega_helper (Subst.(s2 ++ s1 ++ s0 ++ s01 ++ s02 ++ x), hd2 :: tl)
          | Error x -> fail x)
        | s0, [ hd1 ] ->
          let* s01, s1, l1 = hd1 in
          return (Subst.(s1 ++ s0 ++ s01), Subst.apply s0 l1)
        | _ -> fail (Typing_failure_exp (EMatch (exp_main, cases)))
      in
      mega_helper (s0, l)
    | _ -> fail Not_Implemented
  in
  helper
;;

let infer_decl context = function
  | DLet binding ->
    (match binding with
    | false, PVar x, exp ->
      let* s1, t1 = infer_exp context exp in
      let context2 = TypeContext.apply s1 context in
      let t2 = generalize context2 t1 in
      return (TypeContext.extend context2 x t2)
    | true, PVar x, exp ->
      let* fresh = fresh_var in
      let context = TypeContext.extend context x (S (VarSet.empty, fresh)) in
      let* s1, t1 = infer_exp context exp in
      let* _ = unify fresh t1 in
      let context2 = TypeContext.apply s1 context in
      let t2 = generalize context2 t1 in
      return (TypeContext.extend context2 x t2)
    | _ -> fail (Typing_failure_decl (DLet binding)))
  | _ -> fail Not_Implemented
;;

let infer_prog prog =
  let context_empty = return TypeContext.empty in
  let context1 =
    List.fold_left
      (fun context decl ->
        let* context = context in
        infer_decl context decl)
      context_empty
      prog
  in
  match R.run context1 with
  | Ok _ -> true
  | Error x ->
    pp_error std_formatter x;
    false
;;

let test_infer exp =
  match run (infer_exp TypeContext.empty exp) with
  | Ok (s, t) ->
    Subst.pp s;
    Printf.printf "Type is:\n%s\n" (show_tyexp t);
    true
  | Error e ->
    Printf.printf "Error is:\n%s\n" (show_error e);
    false
;;

let test code =
  match Parser.parse Parser.exp code with
  | Result.Ok exp -> test_infer exp
  | _ ->
    Printf.printf "Parse error";
    false
;;

(* let%test _ = test {|

   let rec fold f init l = match l with 
   | [] -> init
   | hd :: tl -> fold f (f init hd) tl
   in fold

   |} *)

(* let%test _ = test {|
   let rec fix f x = f (fix f) x in fix|} *)

(* let%test _ = test {|
   fun x y -> x :: y
   |} *)

(* let%expect_test _ =
   let _ =
    let subst =
      unify
        (TArrow (TArrow (TInt, TString), TArrow (TString, TInt)))
        (TArrow (TArrow (TVar 1, TVar 2), TArrow (TVar 3, TVar 4)))
    in
    let open Caml.Format in
    match R.run subst with
    | Result.Error e -> pp_error std_formatter e
    | Ok subst -> Subst.pp subst
   in
   [%expect {| [ 1 -> int 2 -> int ] |}]
   ;; *)
