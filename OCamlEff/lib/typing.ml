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
  type t = id

  let compare = compare
end)

module SubstMap = Map.Make (struct
  type t = fresh

  let compare = compare
end)

module Subst : sig
  type t

  val empty : t
  val singleton : fresh -> tyexp -> t
  val find : fresh -> t -> tyexp
  val remove : fresh -> t -> t
  val apply : t -> tyexp -> tyexp
  val union : t -> t -> t
  val compose : t -> t -> t
  val ( ++ ) : t -> t -> t
end = struct
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
  ;;

  let free_vars =
    let rec helper acc = function
      | TInt | TBool | TString -> acc
      | TVar x -> VarSet.add x acc
      | TArrow (l, r) -> helper (helper acc l) r
      | TList tyexp -> helper acc tyexp
      | TTuple tyexp_l -> List.fold_left (fun acc tyexp -> helper acc tyexp) acc tyexp_l
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

  let extend id scheme = TypeMap.add id scheme
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
    | TTuple _, TTuple _ -> failwith "unimpl"
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

let infer =
  let rec (helper : TypeContext.t -> exp -> (Subst.t * tyexp) R.t) =
   fun context -> function
    | EConst x ->
      (match x with
      | CInt _ -> return (Subst.empty, TInt)
      | CBool _ -> return (Subst.empty, TBool)
      | CString _ -> return (Subst.empty, TString))
    | EOp (op, exp1, exp2) ->
      let* s1, t1 = helper context exp1 in
      let* s2, t2 = helper context exp2 in
      let* s = unify t1 t2 in
      (match op, exp1, exp2 with
      | Add, _, _ | Sub, _, _ | Mul, _, _ | Div, _, _ ->
        let* s_int = unify t1 TInt in
        let app = Subst.apply Subst.(s ++ s_int) t1 in
        return (Subst.(s ++ s1 ++ s2 ++ s_int), arrow app (arrow app TInt))
      | _, _, _ -> return (Subst.(s1 ++ s2 ++ s), arrow t1 (arrow t1 TBool)))
    | EUnOp (op, exp) ->
      let* s, t = helper context exp in
      (match op with
      | Minus ->
        let* s_int = unify t TInt in
        let app = Subst.apply s_int t in
        return (Subst.(s_int ++ s), arrow app TInt)
      | Not ->
        let* s_bool = unify t TInt in
        let app = Subst.apply s_bool t in
        return (Subst.(s_bool ++ s), arrow app TBool))
    | EVar x ->
      let* subst, tyexp = lookup_context x context in
      return (subst, tyexp)
    | EList exps ->
      (match exps with
      | hd :: tl ->
        let* s1, t1 = helper context hd in
        let* s_tl, t_tl = helper context (EList tl) in
        let* s = unify t1 t_tl in
        return (Subst.(s1 ++ s_tl ++ s), TList (Subst.apply s t1))
      | [] ->
        let* fresh = fresh_var in
        return (Subst.empty, TList fresh))
    | ETuple exps ->
      (match exps with
      | hd :: tl ->
        let* s1, t1 = helper context hd in
        let* s_tl, t_tl = helper context (ETuple tl) in
        (match t_tl with
        | TTuple tyexps -> return (Subst.(s1 ++ s_tl), TTuple (t1 :: tyexps))
        | _ -> failwith "error")
      | [] -> return (Subst.empty, TTuple []))
    | _ -> failwith "unimpl"
  in
  helper
;;

let w e = Result.map (fun (_, t) -> t) (run (infer TypeContext.empty e))

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
;;

let error_to_st = function
  | Occurs_check -> "oc check"
  | NoVariable _ -> "no var"
  | UnificationFailed (x, y) ->
    String.concat " " [ "uni fail:"; tyexp_to_st x; tyexp_to_st y ]
;;

let%test _ =
  match w (EList [ EConst (CInt 5); EConst (CInt 6); EConst (CInt 3) ]) with
  | Error x ->
    Printf.printf "%s\n" (error_to_st x);
    Printf.printf "-----\n";
    false
  | Ok x ->
    Printf.printf "%s\n" (tyexp_to_st x);
    Printf.printf "-----\n";
    true
;;

let%test _ =
  match w (EOp (Add, EConst (CInt 5), EConst (CInt 6))) with
  | Error x ->
    Printf.printf "%s\n" (error_to_st x);
    Printf.printf "-----\n";
    false
  | Ok x ->
    Printf.printf "%s\n" (tyexp_to_st x);
    Printf.printf "-----\n";
    true
;;

let%test _ =
  match w (ETuple [ EConst (CInt 5); EConst (CString "kek") ]) with
  | Error x ->
    Printf.printf "%s\n" (error_to_st x);
    Printf.printf "-----\n";
    false
  | Ok x ->
    Printf.printf "%s\n" (tyexp_to_st x);
    Printf.printf "-----\n";
    true
;;
