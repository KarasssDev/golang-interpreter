open Angstrom
open Ast
open Format

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
  >>= fun s ->
  if is_keyword s
  then fail "Parsing error: keyword reserved"
  else if s = "_"
  then fail "Parsing error: wildcard `_` isn't supported"
  else return s
;;

let ptupple pelm = pparens @@ sep_by (pstoken ",") pelm
let pvarty = ptoken (string "'" *> pid)
let pexc1 = pstoken "Exc1" *> return exc1
let pexc2 = pstoken "Exc2" *> return exc2
let pexc = pexc1 <|> pexc2
let peff_exc = eff_exc <$> pstoken "exc " *> pexc
let peff_io = pstoken "IO" *> return eff_io
let peff_asgmt = pstoken "Asgmt" *> return eff_asgmt
let peff_var = eff_var <$> pvarty
let peff = choice [ peff_exc; peff_io; peff_asgmt; peff_var ]

let peffs =
  (fun l -> EffSet.of_list l)
  <$> choice
        [ (fun _ -> all_effs) <$> pstoken "->"
        ; (fun _ -> []) <$> pstoken "-->"
        ; pstoken "-[" *> sep_by (pstoken ",") peff <* pstoken "]->"
        ]
;;

let ptunit = pstoken "unit" *> return t_unit
let ptint = pstoken "int" *> return t_int
let ptstring = pstoken "string" *> return t_string
let ptbool = pstoken "bool" *> return t_bool
let ptexc = t_exc <$> pexc
let ptlist pty = t_list <$> (pty <* pstoken1 "list")
let ptref pty = t_ref <$> (pty <* pstoken1 "ref")
let ptvar = t_var <$> pvarty
let ptfun = (fun effs ty1 ty2 -> t_fun ty1 effs ty2) <$> peffs
let ptlist = pstoken "list" *> return t_list
let ptref = pstoken "ref" *> return t_ref

let pty =
  fix
  @@ fun pty ->
  let term = choice [ pparens pty; ptunit; ptint; ptstring; ptbool; ptexc; ptvar ] in
  let term =
    lift2
      (fun ty mods -> List.fold_left (fun ty modif -> modif ty) ty mods)
      term
      (many (ptlist <|> ptref))
  in
  let term =
    (fun l ->
      match l with
      | [ ty ] -> ty
      | _ -> t_tuple l)
    <$> sep_by1 (pstoken "*") term
    <|> pstoken "()" *> return t_unit
  in
  chainr1 term ptfun
;;

let psign =
  choice [ pstoken "+" *> return 1; pstoken "-" *> return (-1); pstoken "" *> return 1 ]
;;

let pcint =
  ptoken
  @@ lift2
       (fun sign v -> c_int (sign * v))
       psign
       (take_while is_digit
       >>= fun s ->
       match int_of_string_opt s with
       | Some x -> return x
       | None -> fail "Parsing error: invalid int")
;;

let pcstring =
  c_string <$> ptoken @@ (string "\"" *> take_while (fun ch -> ch != '"')) <* string "\""
;;

let pcbool = c_bool <$> (pstoken "true" *> return true <|> pstoken "false" *> return false)
let pcempty_list = pstoken "[]" *> return c_empty_list
let pconst = choice [ pcint; pcstring; pcbool; pcempty_list ]
let ppval = p_val <$> pid
let ppconst = p_const <$> pconst

let ppatrn =
  fix
  @@ fun ppatrn ->
  let term = choice [ pparens ppatrn; ppconst; ppval ] in
  let term =
    (fun l ->
      match List.rev l with
      | [ p ] -> p
      | hd :: tl -> p_cons (List.rev tl) hd
      | _ -> failwith "Can't happen because of sep_by1")
    <$> sep_by1 (pstoken "::") term
  in
  (fun l ->
    match l with
    | [ p ] -> p
    | _ -> p_tuple l)
  <$> sep_by1 (pstoken ",") term
  <|> pstoken "()" *> return p_unit
;;

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
let peconst = e_const <$> pconst
let peval = e_val <$> pid
let pelet pexpr = lift2 e_let (pdecl_base pexpr) (pstoken1 "in" *> ptoken1 pexpr)

let pematch pexpr =
  lift2
    e_match
    (pstoken "match" *> ptoken1 pexpr <* pstoken1 "with")
    (many1 @@ pcase ppatrn pexpr)
;;

let pparm =
  fix
  @@ fun pparam ->
  pparens pparam <|> lift2 (fun s t -> s, t) (ptoken pid <* pstoken ":") pty
;;

let pefun pexpr =
  pstoken "fun"
  *> lift2 (fun (s, t) e -> e_fun s t e) (ptoken1 pparm <* pstoken "->") pexpr
;;

let peapp pexpr = lift2 e_app pexpr (ptoken1 pexpr)

let petry pexpr =
  lift2
    e_try
    (pstoken "try" *> ptoken1 pexpr <* pstoken1 "with")
    (many1 @@ pcase pexc pexpr)
;;

let pebinop term pbinops =
  chainr1 term ((fun op expr1 expr2 -> e_binop expr1 op expr2) <$> pbinops)
;;

let pmul = pstoken "*" *> return mul
let pdiv = pstoken "/" *> return div
let padd = pstoken "+" *> return add
let psub = pstoken "-" *> return sub
let pcons = pstoken "::" *> return cons
let pneq = pstoken "!=" *> return neq
let peq = pstoken "=" *> return eq
let pleq = pstoken "<=" *> return leq
let ples = pstoken "<" *> return les
let pgeq = pstoken ">=" *> return geq
let pgre = pstoken ">" *> return gre
let pand = pstoken "&&" *> return _and
let por = pstoken "||" *> return _or
let pasgmt = pstoken ":=" *> return asgmt

let pexpr =
  fix (fun pexpr ->
      let term =
        choice [ pstoken "()" *> return e_unit; pparens pexpr; peconst; peval ]
      in
      let term =
        lift2
          (fun l expr -> List.fold_left (fun expr _ -> e_unop deref expr) expr l)
          (many (pstoken "!"))
          term
      in
      let term =
        lift2 (fun expr l -> List.fold_left e_app expr l) term (many (ptoken1 term))
      in
      let term =
        lift2
          (fun l expr -> List.fold_left (fun expr _ -> e_unop neg expr) expr l)
          (many (pstoken "-"))
          term
      in
      let term = pebinop term (pmul <|> pdiv) in
      let term = pebinop term (padd <|> psub) in
      let term = pebinop term pcons in
      let term = pebinop term (choice [ pneq; peq; pleq; ples; pgeq; pgre ]) in
      let term = pebinop term pand in
      let term = pebinop term por in
      let term =
        (fun l ->
          match l with
          | [ expr ] -> expr
          | _ -> ETuple l)
        <$> sep_by1 (pstoken ",") term
      in
      let term = pebinop term pasgmt in
      choice [ pelet pexpr; pematch pexpr; pefun pexpr; petry pexpr; term ])
;;

let pdecl = ptoken (pdecl_base pexpr)
let pdecl_delim = many (pstoken ";;") *> pspace
let pprogram = pdecl_delim *> many (pdecl <* pdecl_delim)
let parse s = parse_string ~consume:Consume.All pprogram s

(* Tests *)

let test_parse str expected =
  match parse str with
  | Error err ->
    printf "%s\n" err;
    false
  | Ok actual ->
    let is_eq = List.equal equal_decl expected actual in
    if is_eq
    then ()
    else (
      printf "Expected: ";
      pp_program std_formatter expected;
      printf "\nActual: ";
      pp_program std_formatter expected;
      printf "\n");
    is_eq
;;

let%test _ = test_parse "" []

let%test _ = test_parse {|
;;;;
;;
;;
|} []

let%test _ =
  test_parse
    {|
let rec map : ('a -['e]-> 'b) --> 'a list -['e]-> 'b list = fun f: ('a -['e]-> 'b) -> fun xs : 'a list ->
  match xs with
  | [] -> []
  | x::xs -> (f x) :: (map f xs)
;;
let id: 'a --> 'a = fun x: 'a -> x
;;
|}
    [ { is_rec = true
      ; name = "map"
      ; ty =
          TFun
            ( TFun (TVar "a", EffSet.of_list [ EffVar "e" ], TVar "b")
            , EffSet.of_list []
            , TFun (TList (TVar "a"), EffSet.of_list [ EffVar "e" ], TList (TVar "b")) )
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
    ; { is_rec = false
      ; name = "id"
      ; ty = TFun (TVar "a", EffSet.of_list [], TVar "a")
      ; expr = EFun ("x", TVar "a", EVal "x")
      }
    ]
;;

let%test _ =
  test_parse
    {|
let rec map2 : ('a --> 'b -['e]-> 'c) --> 'a list --> 'b list -['e, exc Exc1]-> 'c list = 
  fun (f: ('a --> 'b -['e]-> 'c)) ->
    fun l1: 'a list -> fun l2: 'b list ->
  match (l1, l2) with
  | ([], []) -> []
  | (a1::l1, a2::l2) -> let r: 'c = f a1 a2 in r :: map2 f l1 l2
  | (o1, o2) -> raiseExc1 ()
;;
|}
    [ { is_rec = true
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
                            , EApp (EVal "raiseExc1", ETuple []) )
                          ] ) ) ) )
      }
    ]
;;

let%test _ =
  test_parse
    {|
let x: int ref = ref 1
;;
let o: () = x := !x + 1
;;
let result: int = !x
;;
|}
    [ { is_rec = false
      ; name = "x"
      ; ty = TRef TInt
      ; expr = EApp (EVal "ref", EConst (CInt 1))
      }
    ; { is_rec = false
      ; name = "o"
      ; ty = TTuple []
      ; expr =
          EBinop (EVal "x", Asgmt, EBinop (EUnop (Deref, EVal "x"), Add, EConst (CInt 1)))
      }
    ; { is_rec = false; name = "result"; ty = TInt; expr = EUnop (Deref, EVal "x") }
    ]
;;

let%test _ =
  test_parse
    {|
let f: bool -[exc Exc1, exc Exc2]-> string = fun flag: bool ->
  match flag with
  | true -> raiseExc1 ()
  | false -> raiseExc2 ()
;;
let s: string = try f true with
| Exc1 -> raiseExc2 ()
| Exc2 -> "literal"
|}
    [ { is_rec = false
      ; name = "f"
      ; ty = TFun (TBool, EffSet.of_list [ EffExc Exc1; EffExc Exc2 ], TString)
      ; expr =
          EFun
            ( "flag"
            , TBool
            , EMatch
                ( EVal "flag"
                , [ PConst (CBool true), EApp (EVal "raiseExc1", ETuple [])
                  ; PConst (CBool false), EApp (EVal "raiseExc2", ETuple [])
                  ] ) )
      }
    ; { is_rec = false
      ; name = "s"
      ; ty = TString
      ; expr =
          ETry
            ( EApp (EVal "f", EConst (CBool true))
            , [ Exc1, EApp (EVal "raiseExc2", ETuple [])
              ; Exc2, EConst (CString "literal")
              ] )
      }
    ]
;;

let%test _ =
  test_parse
    {|
let b: bool = false || (1 + 3) * 2 + 10 >= 24 / 2 - 1 && 5 + 2 * 2 = 9
|}
    [ { is_rec = false
      ; name = "b"
      ; ty = TBool
      ; expr =
          EBinop
            ( EConst (CBool false)
            , Or
            , EBinop
                ( EBinop
                    ( EBinop
                        ( EBinop
                            ( EBinop (EConst (CInt 1), Add, EConst (CInt 3))
                            , Mul
                            , EConst (CInt 2) )
                        , Add
                        , EConst (CInt 10) )
                    , Geq
                    , EBinop
                        ( EBinop (EConst (CInt 24), Div, EConst (CInt 2))
                        , Sub
                        , EConst (CInt 1) ) )
                , And
                , EBinop
                    ( EBinop
                        ( EConst (CInt 5)
                        , Add
                        , EBinop (EConst (CInt 2), Mul, EConst (CInt 2)) )
                    , Eq
                    , EConst (CInt 9) ) ) )
      }
    ]
;;

let%test _ =
  test_parse
    {|
let x: int = a1, a2 || a3 && a4 != a5 = a6 >= a7 > a8 <= a9 < a10 :: a11 - a12 * -a13 a14 !a15 / a16 + a17
|}
    [ { is_rec = false
      ; name = "x"
      ; ty = TInt
      ; expr =
          ETuple
            [ EVal "a1"
            ; EBinop
                ( EVal "a2"
                , Or
                , EBinop
                    ( EVal "a3"
                    , And
                    , EBinop
                        ( EVal "a4"
                        , Neq
                        , EBinop
                            ( EVal "a5"
                            , Eq
                            , EBinop
                                ( EVal "a6"
                                , Geq
                                , EBinop
                                    ( EVal "a7"
                                    , Gre
                                    , EBinop
                                        ( EVal "a8"
                                        , Leq
                                        , EBinop
                                            ( EVal "a9"
                                            , Les
                                            , EBinop
                                                ( EVal "a10"
                                                , Cons
                                                , EBinop
                                                    ( EVal "a11"
                                                    , Sub
                                                    , EBinop
                                                        ( EBinop
                                                            ( EVal "a12"
                                                            , Mul
                                                            , EBinop
                                                                ( EUnop
                                                                    ( Neg
                                                                    , EApp
                                                                        ( EApp
                                                                            ( EVal "a13"
                                                                            , EVal "a14"
                                                                            )
                                                                        , EUnop
                                                                            ( Deref
                                                                            , EVal "a15"
                                                                            ) ) )
                                                                , Div
                                                                , EVal "a16" ) )
                                                        , Add
                                                        , EVal "a17" ) ) ) ) ) ) ) ) ) )
                )
            ]
      }
    ]
;;
