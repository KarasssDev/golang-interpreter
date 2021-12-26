open Ast

type error =
  | Occurs_check
  | NoVariable of string
  | UnificationFailed of tyexp * tyexp

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
      | other -> other
    in
    helper
  ;;

  let union xs ys = SubstMap.union (fun _ v1 _ -> Some v1) xs ys
  let compose s1 s2 = union (SubstMap.map (apply s1) s2) s2
  let ( ++ ) = compose
end

module Type = struct
  type t = tyexp

  let rec occurs_in v = function
    | TVar x -> x = v
    | TArrow (l, r) -> occurs_in v l || occurs_in v r
    | TInt | TBool | TString -> false
    | TList tyexp -> occurs_in v tyexp
    | TTuple tyexp_l -> List.exists (fun tyexp -> occurs_in v tyexp) tyexp_l
    | _ -> failwith "unimpl"
  ;;

  let free_vars =
    let rec helper acc = function
      | TInt | TBool | TString -> acc
      | TVar x -> VarSet.add x acc
      | TArrow (l, r) -> helper (helper acc l) r
      | TList tyexp -> helper acc tyexp
      | TTuple tyexp_l -> List.fold_left (fun acc tyexp -> helper acc tyexp) acc tyexp_l
      | _ -> failwith "unimpl"
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
    let s2 = VarSet.fold (fun k s -> Subst.remove k s) names sub in
    S (names, Type.apply s2 ty)
  ;;
end

module TypeContext = struct
  type t = scheme TypeMap.t

  let extend context id scheme = TypeMap.add id scheme context
  let empty = TypeMap.empty

  let free_vars t =
    TypeMap.fold (fun _ v acc -> VarSet.union acc (Scheme.free_vars v)) t VarSet.empty
  ;;

  let apply s context = TypeMap.map (Scheme.apply s) context
end

open R
open R.Syntax

let unify l r =
  let rec helper l r =
    match l, r with
    | TInt, TInt | TBool, TBool | TString, TString -> return Subst.empty
    | TList tyexp_1, tyexp_2 | tyexp_1, TList tyexp_2 -> helper tyexp_1 tyexp_2
    | TTuple tyexp_l_1, TTuple tyexp_l_2
      when List.length tyexp_l_1 = List.length tyexp_l_2 ->
      (match tyexp_l_1, tyexp_l_2 with
      | hd1 :: tl1, hd2 :: tl2 ->
        let* subst_hd = helper hd1 hd2 in
        let* subst_tl = helper (TTuple tl1) (TTuple tl2) in
        return (Subst.compose subst_hd subst_tl)
      | _ -> return Subst.empty)
    | TVar b, t when Type.occurs_in b t -> fail Occurs_check
    | TVar a, TVar b when Int.equal a b -> return Subst.empty
    | TVar b, t | t, TVar b -> return (Subst.singleton b t)
    | TArrow (l1, r1), TArrow (l2, r2) ->
      let* subs1 = helper l1 l2 in
      let* subs2 = helper (Type.apply subs1 r1) (Type.apply subs1 r2) in
      return (Subst.compose subs1 subs2)
    | _ -> fail (UnificationFailed (l, r))
  in
  helper l r
;;

let instantiate (S (bs, t)) =
  VarSet.fold_R
    (fun typ name ->
      let* f1 = fresh in
      return @@ Subst.apply (Subst.singleton name (TVar f1)) typ)
    bs
    (return t)
;;

let generalize context tyexp =
  let free = VarSet.diff (Type.free_vars tyexp) (TypeContext.free_vars context) in
  S (free, tyexp)
;;

let lookup_context e xs =
  match TypeMap.find e xs with
  | (exception Caml.Not_found) | (exception Not_found) -> fail (NoVariable e)
  | scheme ->
    let* ans = instantiate scheme in
    return (Subst.empty, ans)
;;

let fresh_var = fresh >>| fun n -> TVar n

let rec tyexp_to_st = function
  | TInt -> "int"
  | TString -> "string"
  | TBool -> "bool"
  | TList tyexp -> String.concat " " [ tyexp_to_st tyexp; "list" ]
  | TArrow (tyexp1, tyexp2) ->
    String.concat " " [ tyexp_to_st tyexp1; "->"; tyexp_to_st tyexp2 ]
  | TVar x -> string_of_int x
  | TTuple l ->
    let line = List.fold_left (fun ln tyexp -> ln ^ ";" ^ tyexp_to_st tyexp) "" l in
    String.concat "" [ "("; line; ")" ]
  | _ -> failwith "unimpl"
;;

let print_subst s =
  let res =
    SubstMap.fold
      (fun k v ln ->
        let new_res =
          ln ^ Printf.sprintf "%s -> %s\n" (string_of_int k) (tyexp_to_st v)
        in
        new_res)
      s
      ""
  in
  Printf.printf "%s" res;
  Printf.printf "%s\n" (string_of_int (SubstMap.cardinal s))
;;

let infer_pat =
  let rec (helper : TypeContext.t -> pat -> (Subst.t * tyexp * TypeContext.t) R.t) =
   fun context -> function
    | PConst x ->
      return
        (match x with
        | CInt _ -> Subst.empty, TInt, TypeContext.empty
        | CBool _ -> Subst.empty, TBool, TypeContext.empty
        | CString _ -> Subst.empty, TString, TypeContext.empty)
    | PCons (pat1, pat2) ->
      let* s1, t1, _ = helper context pat1 in
      let* s2, t2, _ = helper context pat2 in
      (match t2 with
      | TList _ ->
        let* s_uni = unify (TList t1) t2 in
        return (Subst.(s1 ++ s2 ++ s_uni), TList (Subst.apply s_uni t1), TypeContext.empty)
      | _ -> failwith "typing failure")
    | PNil ->
      let* fresh = fresh_var in
      return (Subst.empty, TList fresh, TypeContext.empty)
    | PVar x ->
      let* fresh = fresh_var in
      let context2 = TypeContext.extend context x (S (VarSet.empty, fresh)) in
      return (Subst.empty, fresh, context2)
    | _ -> failwith "unimpl"
  in
  helper
;;

let infer_exp =
  let rec (helper : TypeContext.t -> exp -> (Subst.t * tyexp) R.t) =
   fun context -> function
    | EConst x ->
      return
        (match x with
        | CInt _ -> Subst.empty, TInt
        | CBool _ -> Subst.empty, TBool
        | CString _ -> Subst.empty, TString)
    | EOp (op, exp1, exp2) ->
      let* _, t1 = helper context exp1 in
      let* _, t2 = helper context exp2 in
      let* s = unify t1 t2 in
      (match op, exp1, exp2 with
      | Add, _, _ | Sub, _, _ | Mul, _, _ | Div, _, _ ->
        let* s1_int = unify t1 TInt in
        let* s2_int = unify t2 TInt in
        return (Subst.union s1_int s2_int, TInt)
      | _, _, _ -> return (s, TBool))
    | EUnOp (op, exp) ->
      let* s, t = helper context exp in
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
        let* s1, t1 = helper context hd in
        let* s_tl, t_tl = helper context (ETuple tl) in
        (match t_tl with
        | TTuple tyexps -> return (Subst.(s_tl ++ s1), TTuple (t1 :: tyexps))
        | _ -> failwith "typing failure")
      | [] -> return (Subst.empty, TTuple []))
    | ENil ->
      let* fresh = fresh_var in
      return (Subst.empty, TList fresh)
    | ECons (exp1, exp2) ->
      let* s1, t1 = helper context exp1 in
      let* s2, t2 = helper context exp2 in
      (match t2 with
      | TList _ ->
        let* s_uni = unify (TList t1) t2 in
        return (Subst.(s_uni ++ s1 ++ s2), TList (Subst.apply s_uni t1))
      | _ -> failwith "typing failure")
    | EIf (exp1, exp2, exp3) ->
      let* s1, t1 = helper context exp1 in
      let* s2, t2 = helper context exp2 in
      let* s3, t3 = helper context exp3 in
      let* s4 = unify t1 TBool in
      let* s5 = unify t2 t3 in
      return (Subst.(s5 ++ s4 ++ s3 ++ s2 ++ s1), Subst.apply s5 t2)
    | ELet (bindings, in_exp) ->
      (match bindings with
      | hd :: tl ->
        (match hd with
        | false, PVar x, exp ->
          let* s1, t1 = helper context exp in
          let context2 = TypeContext.apply s1 context in
          let t2 = generalize context2 t1 in
          let* s2, t3 = helper (TypeContext.extend context2 x t2) (ELet (tl, in_exp)) in
          return (Subst.(s1 ++ s2), t3)
        | true, PVar x, exp ->
          let* fresh = fresh_var in
          let context = TypeContext.extend context x (S (VarSet.empty, fresh)) in
          let* s1, t1 = helper context exp in
          let* _ = unify fresh t1 in
          let context2 = TypeContext.apply s1 context in
          let t2 = generalize context2 t1 in
          let* s2, t3 = helper (TypeContext.extend context2 x t2) (ELet (tl, in_exp)) in
          return (Subst.(s1 ++ s2), t3)
        | _ -> failwith "typing error")
      | [] ->
        let* s, t = helper context in_exp in
        return (s, t))
    | EFun (pat, exp) ->
      let* s1, t1, context1 = infer_pat context pat in
      let new_context = TypeMap.union (fun _ v1 _ -> Some v1) context1 context in
      let* s2, t2 = helper new_context exp in
      let s_comp = Subst.(s1 ++ s2) in
      return (s_comp, arrow (Subst.apply s_comp t1) t2)
    | EApp (exp1, exp2) ->
      let* s1, t1 = helper context exp1 in
      let* s2, t2 = helper context exp2 in
      let* s_uni = unify t1 t2 in
      return (Subst.(s1 ++ s2 ++ s_uni), Subst.apply s_uni t2)
    | _ -> failwith "unimpl"
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
    | _ -> failwith "typing error")
  | _ -> failwith "unimpl"
;;

let error_to_st = function
  | Occurs_check -> "oc check"
  | NoVariable x -> String.concat " " [ "no var"; x ]
  | UnificationFailed (x, y) ->
    String.concat " " [ "uni fail:"; tyexp_to_st x; tyexp_to_st y ]
;;

let infer_prog prog =
  let context1 =
    List.fold_left
      (fun context decl ->
        match Result.map (fun t -> t) (run (infer_decl context decl)) with
        | Error x ->
          Printf.printf "%s\n" (error_to_st x);
          failwith "error"
        | Ok x -> x)
      TypeContext.empty
      prog
  in
  context1
;;

let w e = Result.map (fun (_, t) -> t) (run (infer_exp TypeContext.empty e))

let test_infer prog =
  (* try *)
  let context = infer_prog prog in
  TypeMap.iter
    (fun k v ->
      match Result.map (fun t -> t) (run (instantiate v)) with
      | Ok x -> Printf.printf "%s -> %s\n" k (tyexp_to_st x)
      | Error x -> Printf.printf "Some error???: %s\n" (error_to_st x))
    context;
  Printf.printf "-----\n";
  true
;;

(* with
  | Failure _ -> false *)

let test code =
  match Parser.parse Parser.prog code with
  | Result.Ok prog -> test_infer prog
  | _ -> failwith "Parse error"
;;

(* let%test _ =
  test_infer [ DLet (false, PVar "x", ETuple [ EConst (CInt 5); EConst (CInt 6) ]) ]
;;

let%test _ =
  test_infer
    [ DLet
        ( false
        , PVar "x"
        , ECons (EConst (CInt 1), ECons (EConst (CInt 2), ECons (EConst (CInt 5), ENil)))
        )
    ]
;;

let%test _ =
  test_infer
    [ DLet
        (false, PVar "x", EFun (PVar "x", EFun (PVar "y", EOp (Add, EVar "x", EVar "y"))))
    ]
;; *)

let%test _ =
  test
    {|
let x = 2 + 5 + 3 * 4
let y = [x+1;x+2;x+3;x+4]
let c =  5 :: y
let f x y = x + y
|}
;;

let%test _ =
  test
    {|
let x =
     let y =
       let y = 10 in
       5
     in
     y
let tuple = (1, 2, 2) < (1, 2, 3)     
|}
;;

let%test _ = test {|
let id x y = x = y
|}
