open Format

type exc =
  | Exc1
  | Exc2
[@@deriving eq, ord, show { with_path = false }]

let exc1 = Exc1
let exc2 = Exc2

type eff =
  | EffIO
  | EffAsgmt
  | EffExc of exc
  | EffVar of string
[@@deriving eq, ord]

let eff_io = EffIO
let eff_asgmt = EffAsgmt
let eff_exc exc = EffExc exc
let eff_var name = EffVar name
let all_effs = [ eff_exc exc1; eff_exc exc2; eff_io; eff_asgmt ]

let pp_eff fmt = function
  | EffIO -> fprintf fmt "IO"
  | EffAsgmt -> fprintf fmt "Asgmt"
  | EffExc exc -> fprintf fmt "exc %a" pp_exc exc
  | EffVar name -> fprintf fmt "'%s" name
;;

module EffSet = Set.Make (struct
  let compare = compare_eff

  type t = eff
end)

type eff_set = EffSet.t

let pp_eff_set fmt effs =
  pp_print_seq
    ~pp_sep:(fun fmt () -> fprintf fmt ", ")
    (fun fmt eff -> pp_eff fmt eff)
    fmt
    (EffSet.to_seq effs)
;;

let equal_eff_set effs1 effs2 = EffSet.subset effs1 effs2 && EffSet.subset effs2 effs1

type ty =
  | TInt
  | TString
  | TBool
  | TExc of exc
  | TTuple of ty list
  | TList of ty
  | TRef of ty
  | TVar of string
  | TFun of ty * eff_set * ty
[@@deriving eq]

let t_int = TInt
let t_string = TString
let t_bool = TBool
let t_exc exc = TExc exc
let t_tuple tys = TTuple tys
let t_unit = t_tuple []
let t_list ty = TList ty
let t_ref ty = TRef ty
let t_var name = TVar name
let t_fun arg_ty effs ret_ty = TFun (arg_ty, effs, ret_ty)

let rec pp_ty fmt = function
  | TInt -> fprintf fmt "int"
  | TString -> fprintf fmt "string"
  | TBool -> fprintf fmt "bool"
  | TExc exc -> pp_exc fmt exc
  | TTuple tys ->
    fprintf
      fmt
      "(%a)"
      (Format.pp_print_list
         ~pp_sep:(fun fmt () -> fprintf fmt " * ")
         (fun fmt ty -> pp_ty fmt ty))
      tys
  | TList ty -> fprintf fmt "%a list" pp_ty ty
  | TRef ty -> fprintf fmt "%a ref" pp_ty ty
  | TVar name -> fprintf fmt "'%s" name
  | TFun (arg_ty, effs, ret_ty) ->
    fprintf fmt "(%a -[%a]-> %a)" pp_ty arg_ty pp_eff_set effs pp_ty ret_ty
;;

type unop =
  | Neg
  | Deref
[@@deriving eq]

let neg = Neg
let deref = Deref

let rec pp_unop fmt = function
  | Neg -> fprintf fmt "-"
  | Deref -> fprintf fmt "!"
;;

type binop =
  | Add
  | Sub
  | Mul
  | Div
  | Eq
  | Neq
  | Les
  | Leq
  | Gre
  | Geq
  | And
  | Or
  | Asgmt
  | Cons
[@@deriving eq]

let add = Add
let sub = Sub
let mul = Mul
let div = Div
let eq = Eq
let neq = Neq
let les = Les
let leq = Leq
let geq = Geq
let gre = Gre
let _and = And
let _or = Or
let asgmt = Asgmt
let cons = Cons

let rec pp_binop fmt op =
  fprintf
    fmt
    (match op with
    | Add -> "+"
    | Sub -> "-"
    | Mul -> "*"
    | Div -> "/"
    | Eq -> "="
    | Neq -> "!="
    | Les -> "<"
    | Leq -> "<="
    | Gre -> ">"
    | Geq -> ">="
    | And -> "&&"
    | Or -> "||"
    | Asgmt -> ":="
    | Cons -> "::")
;;

type const =
  | CInt of int
  | CString of string
  | CBool of bool
  | CEmptyList
[@@deriving eq]

let c_int n = CInt n
let c_string s = CString s
let c_bool b = CBool b
let c_empty_list = CEmptyList

let rec pp_const fmt = function
  | CInt d -> fprintf fmt "%d" d
  | CString s -> fprintf fmt "%S" s
  | CBool b -> fprintf fmt "%b" b
  | CEmptyList -> fprintf fmt "[]"
;;

type ptrn =
  | PVal of string
  | PConst of const
  | PTuple of ptrn list
  | PCons of ptrn list * ptrn
[@@deriving eq, show { with_path = false }]

let p_val name = PVal name
let p_const const = PConst const
let p_tuple ptrns = PTuple ptrns
let p_unit = p_tuple []
let p_cons ptrns ptrn = PCons (ptrns, ptrn)

let rec pp_ptrn fmt = function
  | PVal s -> fprintf fmt "%s" s
  | PConst c -> pp_const fmt c
  | PTuple l ->
    fprintf fmt "(%a)" (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt ", ") pp_ptrn) l
  | PCons (ptrns, ptrn) ->
    pp_print_list
      ~pp_sep:(fun _ () -> ())
      (fun fmt p -> fprintf fmt "%a :: " pp_ptrn p)
      fmt
      ptrns;
    pp_ptrn fmt ptrn
;;

type decl =
  { is_rec : bool
  ; name : string
  ; ty : ty
  ; expr : expr
  }
[@@deriving eq]

and expr =
  | EConst of const
  | EVal of string
  | EUnop of unop * expr
  | EBinop of expr * binop * expr
  | EApp of expr * expr
  | ETuple of expr list
  | ELet of decl * expr
  | EMatch of expr * (ptrn * expr) list
  | EFun of string * ty * expr
  | ETry of expr * (exc * expr) list
[@@deriving eq]

let e_const const = EConst const
let e_val name = EVal name
let e_unop op expr = EUnop (op, expr)
let e_binop expr1 op expr2 = EBinop (expr1, op, expr2)
let e_app fn arg = EApp (fn, arg)
let e_tuple exprs = ETuple exprs
let e_unit = e_tuple []
let e_let decl expr = ELet (decl, expr)
let e_match scr cases = EMatch (scr, cases)
let e_fun prm_name prm_ty body = EFun (prm_name, prm_ty, body)
let e_try scr cases = ETry (scr, cases)

let rec pp_decl fmt decl =
  fprintf
    fmt
    "let %s%s : %a = %a"
    (if decl.is_rec then "rec " else "")
    decl.name
    pp_ty
    decl.ty
    pp_expr
    decl.expr

and pp_expr fmt = function
  | EConst c -> pp_const fmt c
  | EVal s -> fprintf fmt "%s" s
  | EUnop (op, expr) -> fprintf fmt "(%a%a)" pp_unop op pp_expr expr
  | EBinop (expr1, op, expr2) ->
    fprintf fmt "(%a %a %a)" pp_expr expr1 pp_binop op pp_expr expr2
  | EApp (f, arg) -> fprintf fmt "(%a %a)" pp_expr f pp_expr arg
  | ETuple l ->
    fprintf fmt "(%a)" (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt ", ") pp_expr) l
  | ELet (decl, expr) -> fprintf fmt "%a in\n%a" pp_decl decl pp_expr expr
  | EMatch (scr, ptrns) ->
    fprintf
      fmt
      "match %a with\n%a"
      pp_expr
      scr
      (pp_print_list (fun fmt (p, e) -> fprintf fmt "| %a -> %a" pp_ptrn p pp_expr e))
      ptrns
  | EFun (prm, prmty, expr) ->
    fprintf fmt "fun %s : %a -> %a" prm pp_ty prmty pp_expr expr
  | ETry (scr, excs) ->
    fprintf
      fmt
      "try %a with\n%a"
      pp_expr
      scr
      (pp_print_list (fun fmt (exc, expr) ->
           fprintf fmt "| %a -> %a" pp_exc exc pp_expr expr))
      excs
;;

type program = decl list [@@deriving eq]

let pp_program fmt program =
  pp_print_list (fun fmt decl -> fprintf fmt "%a\n;;\n" pp_decl decl) fmt program
;;
