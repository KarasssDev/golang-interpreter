open Angstrom
open Ast

let is_space = function
  | ' ' | '\t' | '\n' | '\r' -> true
  | _ -> false
;;

let chainl1 e op =
  let rec go acc = lift2 (fun f x -> f acc x) op e >>= go <|> return acc in
  e >>= fun init -> go init
;;

let rec chainr1 e op = e >>= fun a -> op >>= (fun f -> chainr1 e op >>| f a) <|> return a
let pspace = take_while is_space
let pspace1 = take_while1 is_space
let ptoken p = pspace *> p
let ptoken1 p = pspace1 *> p
let pstoken s = ptoken @@ string s
let pstoken1 s = ptoken1 @@ string s
let pparens p = pstoken "(" *> p <* pstoken ")"

let is_lower = function
  | 'a' .. 'z' -> true
  | _ -> false
;;

let is_upper = function
  | 'A' .. 'Z' -> true
  | _ -> false
;;

let is_letter ch = is_lower ch || is_upper ch

let is_digit = function
  | '0' .. '9' -> true
  | _ -> false
;;

let is_keyword = function
  | "and"
  | "as"
  | "assert"
  | "asr"
  | "begin"
  | "class"
  | "constraint"
  | "do"
  | "done"
  | "downto"
  | "else"
  | "end"
  | "exception"
  | "external"
  | "false"
  | "for"
  | "fun"
  | "function"
  | "functor"
  | "if"
  | "in"
  | "include"
  | "inherit"
  | "initializer"
  | "land"
  | "lazy"
  | "let"
  | "lor"
  | "lsl"
  | "lsr"
  | "lxor"
  | "match"
  | "method"
  | "mod"
  | "module"
  | "mutable"
  | "new"
  | "nonrec"
  | "object"
  | "of"
  | "open"
  | "or"
  | "private"
  | "rec"
  | "sig"
  | "struct"
  | "then"
  | "to"
  | "true"
  | "try"
  | "type"
  | "val"
  | "virtual"
  | "when"
  | "while"
  | "with" -> true
  | _ -> false
;;

let pid =
  ptoken
  @@ lift2
       (fun hd tl -> Char.escaped hd ^ tl)
       (satisfy (fun ch -> ch = '_' || is_lower ch))
       (take_while (fun ch -> ch = '_' || is_letter ch || is_digit ch))
  >>= fun s -> if is_keyword s then fail "Parsing error: keyword reserved" else 
      if s = "_" then fail "Wildcard `_` isn't supported" else return s
;;

let ptupple pelm = pparens @@ sep_by (pstoken ",") pelm
let pvarty = ptoken (string "'" *> pid)
let pexc1 = pstoken "Exc1" *> return Exc1
let pexc2 = pstoken "Exc2" *> return Exc2
let pexc = pexc1 <|> pexc2
let peff_exc = (fun e -> EffExc e) <$> pstoken "exc " *> pexc
let peff_io = pstoken "IO" *> return EffIO
let peff_asgmt = pstoken "Asgmt" *> return EffAsgmt
let peff_var = (fun s -> EffVar s) <$> pvarty
let peff = choice [ peff_exc; peff_io; peff_asgmt; peff_var ]

let peffs =
  (fun l -> EffSet.of_list l)
  <$> choice
        [ (fun _ -> [ EffExc Exc1; EffExc Exc2; EffIO; EffAsgmt ]) <$> pstoken "->"
        ; (fun _ -> []) <$> pstoken "-->"
        ; pstoken "-[" *> sep_by (pstoken ",") peff <* pstoken "]->"
        ]
;;

let ptunit = pstoken "unit" *> return (TTuple [])
let ptint = pstoken "int" *> return TInt
let ptstring = pstoken "string" *> return TString
let ptbool = pstoken "bool" *> return TBool
let ptexc = (fun e -> TExc e) <$> pexc
let ptlist pty = (fun ty -> TList ty) <$> (pty <* pstoken1 "list")
let ptref pty = (fun ty -> TRef ty) <$> (pty <* pstoken1 "ref")
let ptvar = (fun s -> TVar s) <$> pvarty
let ptfun = (fun effs ty1 ty2 -> TFun (ty1, effs, ty2)) <$> peffs

let pty =
  fix
  @@ fun pty ->
  let term = choice [ pparens pty; ptunit; ptint; ptstring; ptbool; ptexc; ptvar ] in
  let term =
    lift2
      (fun ty mods ->
        List.fold_left
          (fun ty modif ->
            match modif with
            | "list" -> TList ty
            | "ref" -> TRef ty
            | _ -> failwith "Unknown type modifer")
          ty
          mods)
      term
      (many (pstoken "list" <|> pstoken "ref"))
  in
  let term =
    (fun l ->
      match l with
      | [ ty ] -> ty
      | _ -> TTuple l)
    <$> sep_by1 (pstoken "*") term
    <|> pstoken "()" *> return (TTuple [])
  in
  chainr1 term ptfun
;;

let parse_with p s = parse_string ~consume:Consume.All (p <* pspace) s
(* let punop = choice [ pstoken "-" *> return Neg; pstoken "!" *> return Not ] *)

let pbinop =
  choice
    [ pstoken "+" *> return Add
    ; pstoken "-" *> return Sub
    ; pstoken "*" *> return Mul
    ; pstoken "/" *> return Div
    ; pstoken "=" *> return Eq
    ; pstoken "!=" *> return Neq
    ; pstoken "<" *> return Les
    ; pstoken "<=" *> return Leq
    ; pstoken ">" *> return Gre
    ; pstoken ">=" *> return Geq
    ; pstoken "&&" *> return And
    ; pstoken "||" *> return Or
    ; pstoken ":=" *> return Asgmt
    ; pstoken "::" *> return Cons
    ]
;;

let psign =
  choice [ pstoken "+" *> return 1; pstoken "-" *> return (-1); pstoken "" *> return 1 ]
;;

let pcint =
  ptoken
  @@ lift2
       (fun sign v -> CInt (sign * v))
       psign
       (take_while is_digit
       >>= fun s ->
       match int_of_string_opt s with
       | Some x -> return x
       | None -> fail "Parsing error: invalid int")
;;

let pcstring =
  (fun s -> CString s)
  <$> ptoken @@ (string "\"" *> take_while (fun ch -> ch != '"'))
  <* string "\""
;;

let pcbool =
  pstoken "true" *> return (CBool true) <|> pstoken "false" *> return (CBool false)
;;

let pcempty_list = pstoken "[]" *> return CEmptyList
let pconst = choice [ pcint; pcstring; pcbool; pcempty_list ]
let ppval = (fun s -> PVal s) <$> pid
let ppconst = (fun c -> PConst c) <$> pconst

(* let pptupple ppatrn = (fun l -> PTuple l) <$> ptupple ppatrn *)
(* let ppcons = pcons *> return (fun p1 p2 -> PCons (p1, p2)) *)

(* pattern for unit () *)
let ppatrn =
  fix
  @@ fun ppatrn ->
  let term = choice [ pparens ppatrn; ppconst; ppval ] in
  let term =
    (fun l ->
      match List.rev l with
      | [ p ] -> p
      | hd :: tl -> PCons (List.rev tl, hd)
      | _ -> failwith "Can't happen because of sep_by1")
    <$> sep_by1 (pstoken "::") term
  in
  (fun l ->
    match l with
    | [ p ] -> p
    | _ -> PTuple l)
  <$> sep_by1 (pstoken ",") term
  <|> pstoken "()" *> return (PTuple [])
;;

(* TODO remove if fails *)

let pdecl_base pexpr =
  pstoken "let"
  *> lift4
       (fun is_rec name ty expr -> { is_rec; name; ty; expr })
       (pstoken1 "rec" *> return true <|> return false)
       (ptoken1 pid)
       (pstoken ":" *> pty)
       (pstoken "=" *> pexpr)
;;

let pcase pkey pexpr = lift2 (fun k v -> k, v) (pstoken "|" *> pkey <* pstoken "->") pexpr
let peconst = (fun c -> EConst c) <$> pconst
let peval = (fun s -> EVal s) <$> pid
(* let peunop pexpr = lift2 (fun op expr -> EUnop (op, expr)) punop pexpr *)

(* let pebinop pexpr =
  lift3 (fun expr1 op expr2 -> EBinop (expr1, op, expr2)) pexpr pbinop pexpr
;; *)

(* let petupple pexpr = (fun l -> ETuple l) <$> ptupple pexpr *)

let pelet pexpr =
  lift2 (fun s expr -> ELet (s, expr)) (pdecl_base pexpr) (pstoken1 "in" *> ptoken1 pexpr)
;;

let pematch pexpr =
  lift2
    (fun expr cases -> EMatch (expr, cases))
    (pstoken "match" *> ptoken1 pexpr <* pstoken1 "with")
    (many1 @@ pcase ppatrn pexpr)
;;

let pefun pexpr =
  pstoken "fun"
  *> lift3
       (fun s ty expr -> EFun (s, ty, expr))
       (ptoken1 pid <* pstoken ":")
       (pty <* pstoken "->")
       pexpr
;;

let peapp pexpr = lift2 (fun f arg -> EApp (f, arg)) pexpr (ptoken1 pexpr)
(* let peraise pexpr = pstoken "raise" *> ((fun e -> ERaise e) <$> pexpr) *)

let petry pexpr =
  lift2
    (fun expr cases -> ETry (expr, cases))
    (pstoken "try" *> ptoken1 pexpr <* pstoken1 "with")
    (many1 @@ pcase pexc pexpr)
;;

let pebinop term pbinops =
  chainl1 term ((fun op expr1 expr2 -> EBinop (expr1, op, expr2)) <$> pbinops)
;;

(* type dispatch =
  { pexpr : dispatch -> expr t
  ; pprim : dispatch -> expr t
  ; pelet : dispatch -> expr t
  ; pematch : dispatch -> expr t
  ; pefun : dispatch -> expr t
  ; petry : dispatch -> expr t
  }

let pack =
  let pexpr pack =
    fix (fun _ ->
        choice
          [ pack.pprim pack
          ; pack.pelet pack
          ; pack.pematch pack
          ; pack.pefun pack
          ; pack.petry pack
          ])
  in
  let pprim pack =
    fix (fun _ ->
        let term = choice [ pparens (pack.pexpr pack); peconst; peval ] in
        let term =
          lift2
            (fun l expr -> List.fold_left (fun expr _ -> EUnop (Deref, expr)) expr l)
            (many (pstoken "!"))
            term
        in
        let term =
          lift2
            (fun expr l -> List.fold_left (fun f arg -> EApp (f, arg)) expr l)
            term
            (many (ptoken1 term))
        in
        let term =
          lift2
            (fun l expr -> List.fold_left (fun expr _ -> EUnop (Neg, expr)) expr l)
            (many (pstoken "-"))
            term
        in
        let term =
          pebinop term (choice [ pstoken "*" *> return Mul; pstoken "/" *> return Div ])
        in
        let term =
          pebinop term (choice [ pstoken "+" *> return Add; pstoken "-" *> return Sub ])
        in
        let term = pebinop term (choice [ pstoken "::" *> return Cons ]) in
        let term =
          pebinop
            term
            (choice
               [ pstoken "=" *> return Eq
               ; pstoken "!=" *> return Neq
               ; pstoken "<" *> return Les
               ; pstoken "<=" *> return Leq
               ; pstoken ">" *> return Gre
               ; pstoken ">=" *> return Geq
               ])
        in
        let term = pebinop term (choice [ pstoken "&&" *> return And ]) in
        let term = pebinop term (choice [ pstoken "||" *> return Or ]) in
        let term =
          (fun l ->
            match l with
            | [ expr ] -> expr
            | _ -> ETuple l)
          <$> sep_by1 (pstoken ",") term
        in
        pebinop term (choice [ pstoken ":=" *> return Asgmt ]))
  in
  let pelet pack = fix (fun _ -> pelet (pack.pexpr pack)) in
  let pematch pack = fix (fun _ -> pematch (pack.pexpr pack)) in
  let pefun pack = fix (fun _ -> pefun (pack.pexpr pack)) in
  let petry pack = fix (fun _ -> petry (pack.pexpr pack)) in
  { pexpr; pprim; pelet; pematch; pefun; petry }
;; *)

(* TODO unit () expr *)
let pexpr =
  fix (fun pexpr ->
      let term =
        choice [ pstoken "()" *> return (ETuple []); pparens pexpr; peconst; peval ]
      in
      let term =
        lift2
          (fun l expr -> List.fold_left (fun expr _ -> EUnop (Deref, expr)) expr l)
          (many (pstoken "!"))
          term
      in
      let term =
        lift2
          (fun expr l -> List.fold_left (fun f arg -> EApp (f, arg)) expr l)
          term
          (many (ptoken1 term))
      in
      let term =
        lift2
          (fun l expr -> List.fold_left (fun expr _ -> EUnop (Neg, expr)) expr l)
          (many (pstoken "-"))
          term
      in
      let term =
        pebinop term (choice [ pstoken "*" *> return Mul; pstoken "/" *> return Div ])
      in
      let term =
        pebinop term (choice [ pstoken "+" *> return Add; pstoken "-" *> return Sub ])
      in
      let term = pebinop term (choice [ pstoken "::" *> return Cons ]) in
      let term =
        pebinop
          term
          (choice
             [ pstoken "!=" *> return Neq
             ; pstoken "=" *> return Eq
             ; pstoken "<=" *> return Leq
             ; pstoken "<" *> return Les
             ; pstoken ">=" *> return Geq
             ; pstoken ">" *> return Gre
             ])
      in
      let term = pebinop term (choice [ pstoken "&&" *> return And ]) in
      let term = pebinop term (choice [ pstoken "||" *> return Or ]) in
      let term =
        (fun l ->
          match l with
          | [ expr ] -> expr
          | _ -> ETuple l)
        <$> sep_by1 (pstoken ",") term
      in
      let term = pebinop term (choice [ pstoken ":=" *> return Asgmt ]) in
      choice [ pelet pexpr; pematch pexpr; pefun pexpr; petry pexpr; term ])
;;

(* let pexpr =
  fix
  @@ fun pexpr ->
  let term = choice [ pparens pexpr; peconst; peval ] in
  let term =
    lift2
      (fun l expr -> List.fold_left (fun expr _ -> EUnop (Deref, expr)) expr l)
      (many (pstoken "!"))
      term
  in
  let term =
    lift2
      (fun expr l -> List.fold_left (fun f arg -> EApp (f, arg)) expr l)
      term
      (many (ptoken1 term))
  in
  let term =
    lift2
      (fun l expr -> List.fold_left (fun expr _ -> EUnop (Neg, expr)) expr l)
      (many (pstoken "-"))
      term
  in
  let term =
    pebinop term (choice [ pstoken "*" *> return Mul; pstoken "/" *> return Div ])
  in
  let term =
    pebinop term (choice [ pstoken "+" *> return Add; pstoken "-" *> return Sub ])
  in
  let term = pebinop term (choice [ pstoken "::" *> return Cons ]) in
  let term =
    pebinop
      term
      (choice
         [ pstoken "=" *> return Eq
         ; pstoken "!=" *> return Neq
         ; pstoken "<" *> return Les
         ; pstoken "<=" *> return Leq
         ; pstoken ">" *> return Gre
         ; pstoken ">=" *> return Geq
         ])
  in
  let term = pebinop term (choice [ pstoken "&&" *> return And ]) in
  let term = pebinop term (choice [ pstoken "||" *> return Or ]) in
  let term =
    (fun l ->
      match l with
      | [ expr ] -> expr
      | _ -> ETuple l)
    <$> sep_by1 (pstoken ",") term
  in
  let term = pebinop term (choice [ pstoken ":=" *> return Asgmt ]) in
  fix @@ fun p -> choice [
    pelet p;
    p;
    term
  ]
;; *)

(* choice
    [ peconst
    ; peval
    ; peunop pexpr
    ; pebinop pexpr
    ; petupple pexpr
    ; pelet pexpr
    ; pematch pexpr
    ; pefun pexpr
    ; peapp pexpr
    ; peraise pexpr
    ; petry pexpr
    ] *)

let pdecl = ptoken (pdecl_base pexpr)
let pdecl_delim = many (pstoken ";;") *> pspace
let pprogram = pdecl_delim *> many (pdecl <* pdecl_delim)

(* FIXME sep_by *)
let parse s = parse_string ~consume:Consume.All pprogram s

(* TODO: implement parser here

type 'name t = 'name Ast.t =
  | Var of 'name
  | Abs of 'name * 'name t
  | App of 'name t * 'name t
[@@deriving show { with_path = false }]

let pp =
  let mangle t fmt x =
    if is_free_in x t then Format.fprintf fmt "%s" x else Format.fprintf fmt "_"
  in
  let rec pp fmt = function
    | Var s -> Format.fprintf fmt "%s" s
    | App (l, r) -> Format.fprintf fmt "(%a %a)" pp l pp r
    | Abs (x, Abs (y, Var z)) when x = z && y <> z -> Format.fprintf fmt "⊤"
    | Abs (x, Abs (y, Var z)) when y = z && x <> z -> Format.fprintf fmt "⊥"
    | Abs (f, Abs (x, Var z)) when x = z && x <> f -> Format.fprintf fmt "0"
    | Abs (f, Abs (x, App (Var g, Var z))) when x = z && x <> f && g = f ->
      Format.fprintf fmt "1"
    | Abs (f, Abs (x, App (Var g, App (Var h, Var z))))
      when x = z && x <> f && g = f && h = g -> Format.fprintf fmt "2"
    | Abs (v1, Abs (v2, Abs (v3, Abs (v4, t)))) ->
      Format.fprintf
        fmt
        "(λ %a %a %a %a -> %a)"
        (mangle t)
        v1
        (mangle t)
        v2
        (mangle t)
        v3
        (mangle t)
        v4
        pp
        t
    | Abs (v1, Abs (v2, Abs (v3, t))) ->
      Format.fprintf
        fmt
        "(λ %a %a %a -> %a)"
        (mangle t)
        v1
        (mangle t)
        v2
        (mangle t)
        v3
        pp
        t
    | Abs (v1, Abs (v2, t)) ->
      Format.fprintf fmt "(λ %a %a -> %a)" (mangle t) v1 (mangle t) v2 pp t
    | Abs (x, t) -> Format.fprintf fmt "(λ %a -> %a)" (mangle t) x pp t
  in
  pp
;;

let is_space = function
  | ' ' | '\t' | '\n' | '\r' -> true
  | _ -> false
;;

let spaces = skip_while is_space

let varname =
  satisfy (function
      | 'a' .. 'z' -> true
      | _ -> false)
;;

let conde = function
  | [] -> fail "empty conde"
  | h :: tl -> List.fold_left ( <|> ) h tl
;;

type dispatch =
  { apps : dispatch -> char Ast.t Angstrom.t
  ; single : dispatch -> char Ast.t Angstrom.t
  }

let parse_lam =
  let single pack =
    fix (fun _ ->
        conde
          [ char '(' *> pack.apps pack <* char ')'
          ; ((string "λ" <|> string "\\") *> spaces *> varname
            <* spaces
            <* char '.'
            >>= fun var -> pack.apps pack >>= fun b -> return (Ast.Abs (var, b)))
          ; (varname <* spaces >>= fun c -> return (Ast.Var c))
          ])
  in
  let apps pack =
    many1 (spaces *> pack.single pack <* spaces)
    >>= function
    | [] -> fail "bad syntax"
    | x :: xs -> return @@ List.fold_left (fun l r -> Ast.App (l, r)) x xs
  in
  { single; apps }
;;

let parse = Angstrom.parse_string (parse_lam.apps parse_lam) ~consume:Angstrom.Consume.All
let parse_optimistically str = Result.get_ok (parse str)
let pp = Printast.pp Format.pp_print_char

let%expect_test _ =
  Format.printf "%a" pp (parse_optimistically "x y");
  [%expect {| App (Var (x), Var (y)) |}]
;;

let%expect_test _ =
  Format.printf "%a" pp (parse_optimistically "(x y)");
  [%expect {| App (Var (x), Var (y)) |}]
;;

let%expect_test _ =
  Format.printf "%a" pp (parse_optimistically "(\\x . x x)");
  [%expect {| Abs (x, App (Var (x), Var (x))) |}]
;;

let%expect_test _ =
  Format.printf "%a" pp (parse_optimistically "(λf.λx. f (x x))");
  [%expect {| Abs (f, Abs (x, App (Var (f), App (Var (x), Var (x))))) |}]
;; *)
