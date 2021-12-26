open Angstrom
open Ast
open Base

(*-------------- Main --------------*)

let parse p s = parse_string ~consume:All p s

(*-------------- Combinators --------------*)

let chainl1 e op =
  let rec go acc = lift2 (fun f x -> f acc x) op e >>= go <|> return acc in
  e >>= go
;;

let rec chainr1 e op = e >>= fun a -> op >>= (fun f -> chainr1 e op >>| f a) <|> return a

(* chailr1 but parser of most right exp is [pr] *)
let procr op pl pr =
  let p =
    fix @@ fun p -> pl >>= fun l -> op >>= (fun op -> p <|> pr >>| op l) <|> return l
  in
  p
;;

(* chainl1 but parser of most right exp is [pr] *)
let procl op pl pr =
  let rec go acc =
    lift2 (fun f x -> f acc x) op (choice [ pl >>= go; pr ]) <|> return acc
  in
  pl >>= go
;;

(*-------------- Utility and tokens --------------*)

let is_empty = function
  | ' ' | '\t' | '\r' | '\n' -> true
  | _ -> false
;;

let is_digit = function
  | '0' .. '9' -> true
  | _ -> false
;;

let is_lower = function
  | 'a' .. 'z' -> true
  | _ -> false
;;

let is_upper = function
  | 'A' .. 'Z' -> true
  | _ -> false
;;

let is_wild = function
  | '_' -> true
  | _ -> false
;;

let is_idchar c = is_digit c || is_lower c || is_upper c || is_wild c

let is_keyword = function
  | "let"
  | "in"
  | "true"
  | "false"
  | "rec"
  | "fun"
  | "if"
  | "else"
  | "then"
  | "with"
  | "effect"
  | "function"
  | "match" -> true
  | _ -> false
;;

let empty = take_while is_empty
let empty1 = take_while1 is_empty
let trim p = empty *> p <* empty
let token s = empty *> string s

let kwd s =
  token s
  <* (peek_char
     >>| function
     | Some x when is_idchar x -> fail "Incorrect kwd"
     | _ -> return None)
;;

let lp = token "("
let rp = token ")"
let rsb = token "]"
let lsb = token "["
let comma = token ","
let colon = token ":"
let semi = token ";"
let semisemi = token ";;"
let bar = token "|"
let arrow = token "->"
let between l r p = l *> p <* r
let parens p = lp *> p <* rp

(*-------------- Const ctors --------------*)

let cint n = CInt n
let cbool b = CBool b
let cstring s = CString s

(*-------------- Exp ctors --------------*)

let econst c = EConst c
let eunop o e = EUnOp (o, e)
let evar id = EVar id
let etuple l = ETuple l
let econs e1 e2 = ECons (e1, e2)
let eif e1 e2 e3 = EIf (e1, e2, e3)
let elet binds e = ELet (binds, e)
let efunction cases = EFun (PVar "match", EMatch (EVar "match", cases))
let efun p e = EFun (p, e)
let eapp = return (fun e1 e2 -> EApp (e1, e2))
let ematch e cases = EMatch (e, cases)
let efun args rhs = List.fold_right args ~f:efun ~init:rhs
let eop o e1 e2 = EOp (o, e1, e2)
let elist = List.fold_right ~f:econs ~init:ENil
let eeff1 id = EEffect1 id
let eeff2 id exp = EEffect2 (id, exp)

(*-------------- Case ctors --------------*)
let ccase p e = p, e

(*-------------- Binding ctors --------------*)

let bbind isrec p e = isrec, p, e

(*-------------- Pat ctors --------------*)

let pwild _ = PWild
let pvar id = PVar id
let pconst c = PConst c
let ptuple l = PTuple l
let popcons = token "::" *> return (fun p1 p2 -> PCons (p1, p2))
let pcons = return @@ fun p1 p2 -> PCons (p1, p2)
let plist = List.fold_right ~f:(fun p1 p2 -> PCons (p1, p2)) ~init:PNil
let peff1 id = PEffect1 id
let peff2 id pat = PEffect2 (id, pat)
let peffh k pat = PEffectH (k, pat)

(*-------------- Decl ctors --------------*)

let dlet isrec p e = DLet (isrec, p, e)
let deff1 id t1 = DEffect1 (id, t1)
let deff2 id t1 t2 = DEffect2 (id, t1, t2)

(*-------------- Plain parsers --------------*)

let choice_op ops =
  choice @@ List.map ~f:(fun (tok, cons) -> token tok *> (return @@ eop cons)) ops
;;

let add_sub = choice_op [ "+", Add; "-", Sub ]
let mult_div = choice_op [ "*", Mul; "/", Div ]
let cmp = choice_op [ ">=", Geq; ">", Gre; "<=", Leq; "<", Less ]
let eq_uneq = choice_op [ "=", Eq; "<>", Neq ]
let conj = choice_op [ "&&", And ]
let disj = choice_op [ "||", Or ]
let cons = token "::" *> return econs

let app_unop p =
  choice
    [ token "-" *> p >>| eunop Minus; kwd "not" *> p >>| eunop Not; token "+" *> p; p ]
;;

let id valid_fst =
  let* fst = empty *> satisfy valid_fst in
  let take_func =
    match fst with
    | '_' -> many1
    | _ -> many
  in
  let* inner = take_func @@ satisfy is_idchar in
  let id = Base.String.of_char_list @@ (fst :: inner) in
  if is_keyword id then fail "Keyword" else return id
;;

let ident =
  id
  @@ function
  | 'a' .. 'z' | '_' -> true
  | _ -> false
;;

let capitalized_ident =
  id
  @@ function
  | 'A' .. 'Z' -> true
  | _ -> false
;;

(*-------------- Const parsing --------------*)

let uns = trim @@ take_while1 is_digit

let cunsint =
  let* uns = uns in
  return @@ Base.Int.of_string uns >>| cint
;;

let cint =
  let* sgn = option "" (token "+" <|> token "-") in
  let* uns = uns in
  return @@ Base.Int.of_string (sgn ^ uns) >>| cint
;;

let cbool =
  let _true = kwd "true" *> return (cbool true) in
  let _false = kwd "false" *> return (cbool false) in
  _true <|> _false
;;

let cstring =
  between (char '"') (char '"')
  @@ take_while (function
         | '"' -> false
         | _ -> true)
  >>| cstring
;;

let const = trim @@ choice [ cint; cbool; cstring ]
let uns_const = trim @@ choice [ cunsint; cbool; cstring ]

(*-------------- Continuation and effect parsing --------------*)
let pure_or_parens p =
  let helper = fix @@ fun helper -> parens helper <|> p in
  helper
;;

(*-------------- Pattern parsing --------------*)

let pvar = ident >>| pvar
let pwild = token "_" >>| pwild
let pconst = const >>| pconst

type pdispatch =
  { tuple: pdispatch -> pat t
  ; other: pdispatch -> pat t
  ; pat: pdispatch -> pat t
  }

let pack =
  let pat d = fix @@ fun _self -> trim @@ choice [ d.tuple d; d.other d ] in
  let tuple d =
    fix
    @@ fun _self ->
    trim @@ lift2 (fun hd tl -> hd :: tl) (d.other d) (many1 (comma *> d.other d))
    >>| ptuple
  in
  let other d =
    fix
    @@ fun _self ->
    let plist = trim @@ between lsb rsb @@ sep_by semi @@ d.pat d >>| plist in
    let prim = trim @@ choice [ pconst; pvar; pwild; plist; parens @@ d.pat d ] in
    let peff1 = capitalized_ident >>| peff1 in
    let peff2 = lift2 peff2 capitalized_ident prim in
    let peffh = lift2 peffh (kwd "effect" *> (peff1 <|> prim)) ident in
    trim @@ chainr1 (choice [ peffh; peff2; peff1; prim ]) popcons
  in
  { tuple; other; pat }
;;

let pat = pack.pat pack

(*-------------- Expr parsing --------------*)

let rec try_econtinue = function
  | EApp (EApp (EVar "continue", EVar k), e) -> EContinue (k, e)
  | EApp (e1, e2) -> EApp (try_econtinue e1, e2)
  | e -> e
;;

let rec try_eperform = function
  | EApp (EVar "perform", e) -> EPerform e
  | EApp (e1, e2) -> EApp (try_eperform e1, e2)
  | e -> e
;;

type edispatch =
  { key: edispatch -> exp t
  ; tuple: edispatch -> exp t
  ; exp: edispatch -> exp t
  ; op: edispatch -> exp t
  }

let pack =
  let exp d = fix @@ fun _self -> trim @@ d.key d <|> d.tuple d <|> d.op d in
  let key d =
    fix
    @@ fun _self ->
    let eif =
      trim
      @@ lift3 eif (kwd "if" *> d.exp d) (kwd "then" *> d.exp d) (kwd "else" *> d.exp d)
    in
    let elet =
      let binding =
        trim
        @@ lift3
             bbind
             (kwd "let" *> option false (kwd "rec" >>| fun _ -> true))
             pat
             (lift2 efun (empty *> many pat <* token "=") (d.exp d <* kwd "in"))
      in
      trim @@ lift2 elet (many1 binding) (d.exp d)
    in
    let efun = trim @@ lift2 efun (kwd "fun" *> many pat <* arrow) (d.exp d) in
    let ematch =
      let fst_case = lift2 ccase (option "" bar *> pat <* arrow) (d.exp d) in
      let other_cases = lift2 ccase (bar *> pat <* arrow) (d.exp d) in
      let cases = lift2 (fun fst other -> fst :: other) fst_case (many other_cases) in
      let pmatch = lift2 ematch (kwd "match" *> d.exp d <* kwd "with") cases in
      let pfunction = kwd "function" *> cases >>| efunction in
      trim @@ pfunction <|> pmatch
    in
    choice [ elet; eif; ematch; efun ]
  in
  let tuple d =
    lift2 ( @ ) (many1 (d.op d <* comma)) (d.op d <|> d.key d >>| fun rhs -> [ rhs ])
    >>| etuple
  in
  let op d =
    fix
    @@ fun _self ->
    let lst = trim @@ between lsb rsb @@ sep_by semi (d.exp d) in
    let prim =
      trim
      @@ choice [ lst >>| elist; uns_const >>| econst; ident >>| evar; parens @@ d.exp d ]
    in
    let eeff =
      let eeff1 = capitalized_ident >>| eeff1 in
      let eeff2 = lift2 eeff2 capitalized_ident prim in
      eeff2 <|> eeff1
    in
    let app_op =
      trim @@ chainl1 (prim <|> eeff) eapp >>| try_eperform >>| try_econtinue
    in
    let mul_op = procl mult_div app_op @@ d.key d in
    let add_op = procl add_sub (app_unop mul_op) (app_unop @@ d.key d) in
    let cons_op = procr cons add_op @@ d.key d in
    let cmp_op = procl cmp cons_op @@ d.key d in
    let eq_op = procl eq_uneq cmp_op @@ d.key d in
    let conj_op = procl conj eq_op @@ d.key d in
    trim @@ procl disj conj_op @@ d.key d
  in
  { key; tuple; exp; op }
;;

let exp = pack.exp pack

(*-------------- Type parsing --------------*)

type tydispatch =
  { tyexp: tydispatch -> tyexp t
  ; prim: tydispatch -> tyexp t
  }

let pack =
  let prim d =
    fix
    @@ fun _self ->
    let basic =
      trim
      @@ choice
           [ token "int" *> return TInt
           ; token "string" *> return TString
           ; token "bool" *> return TBool
           ; (uns >>| fun bind -> TVar (Base.Int.of_string bind))
           ; parens @@ d.tyexp d
           ]
    in
    let list =
      let* lst_ty = basic in
      let* l = many1 @@ (empty *> token "list") in
      let rec wrap acc n =
        match n with
        | 0 -> acc
        | _ -> wrap (TList acc) (n - 1)
      in
      return @@ wrap lst_ty (List.length l)
    in
    sep_by1 (token "*" *> empty) (list <|> basic)
    >>| function
    | [ a ] -> a
    | tup -> TTuple tup
  in
  let tyexp d =
    fix
    @@ fun _self ->
    trim @@ chainr1 (d.prim d) (arrow *> return (fun t1 t2 -> TArrow (t1, t2)))
  in
  { tyexp; prim }
;;

let tyexp = pack.tyexp pack
let ty1 = pack.prim pack
let ty2 = lift2 (fun t1 t2 -> t1, t2) (ty1 <* arrow) ty1

(*-------------- Decl parsing --------------*)

let decl =
  let dlet =
    lift3
      dlet
      (kwd "let" *> option false (kwd "rec" >>| fun _ -> true))
      pat
      (lift2 efun (empty *> many pat <* token "=") exp)
  in
  let deff2 =
    lift3 deff2 (trim (kwd "effect" *> capitalized_ident)) (colon *> ty1) (arrow *> ty1)
  in
  let deff1 = lift2 deff1 (trim (kwd "effect" *> capitalized_ident)) (colon *> ty1) in
  trim @@ choice [ dlet; deff2; deff1 ]
;;

(*-------------- Prog parsing --------------*)

let pprog (l : decl list) : prog = l
let prog = many1 (trim @@ decl <* trim @@ option "" semisemi) >>| pprog
