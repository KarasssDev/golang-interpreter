open Angstrom
open Ast
open Typing
open Format

(****************** Main parser ******************)

let parse p s = parse_string ~consume:All p s

(****************** Utils for testing ******************)

let parse_test_suc pp p s expected =
  match parse p s with
  | Error _ -> false
  | Result.Ok res ->
    if expected = res
    then true
    else (
      print_string "Actual is:\n";
      pp std_formatter res;
      false)
;;

let parse_test_fail pp p s =
  match parse p s with
  | Error _ -> true
  | Result.Ok res ->
    print_string "Actual is:\n";
    pp std_formatter res;
    false
;;

(****************** Helpers ******************)
let chainl1 e op =
  let rec go acc = lift2 (fun f x -> f acc x) op e >>= go <|> return acc in
  e >>= fun init -> go init
;;

let rec chainr1 e op = e >>= fun a -> op >>= (fun f -> chainr1 e op >>| f a) <|> return a
let mklist a = [ a ]

let is_ws = function
  | ' ' | '\t' -> true
  | _ -> false
;;

let is_eol = function
  | '\r' | '\n' -> true
  | _ -> false
;;

let is_digit = function
  | '0' .. '9' -> true
  | _ -> false
;;

let skip = take_while (fun c -> is_ws c || is_eol c)

let is_keyword = function
  | "let"
  | "in"
  | "true"
  | "false"
  | "rec"
  | "fun"
  | "perform"
  | "if"
  | "continue"
  | "else"
  | "then"
  | "with"
  | "match" -> true
  | _ -> false
;;

let take_all = take_while (fun _ -> true)
let ws = take_while is_ws
let ws1 = take_while1 is_ws
let eol = take_while is_eol
let token s = ws *> string s
let rp = token ")"
let lp = token "("
let rsb = token "]"
let lsb = token "["
let comma = token ","
let semicol = token ";"
let between l r p = l *> p <* r
let parens p = between lp rp p

(****************** Tokens ******************)

let tlistcons = token "::"
let tthen = token "then"
let telse = token "else"
let tif = token "if"
let tfun = token "fun"
let tin = token "in"
let ttrue = token "true"
let tfalse = token "false"
let tlet = token "let"
let teol = token "\n"
let trec = token "rec"
let twild = token "_"
let tmatch = token "match"
let tbar = token "|"
let twith = token "with"
let tarrow = token "->"

(****************** Const ctors ******************)

let cint n = CInt n
let cbool b = CBool b
let cstring s = CString s

(****************** Exp ctors ******************)

let econst c = EConst c
let eop o e1 e2 = EOp (o, e1, e2)
let add = token "+" *> return (eop Add)
let sub = token "-" *> return (eop Sub)
let div = token "/" *> return (eop Div)
let mul = token "*" *> return (eop Mul)
let less = token "<" *> return (eop Less)
let _and = token "&&" *> return (eop And)
let eopcons = token "::" *> return (fun e1 e2 -> ECons (e1, e2))
let _or = token "||" *> return (eop Or)
let eunop o e = EUnOp (o, e)
let evar id = EVar id
let elist l = EList l
let etuple l = ETuple l
let econs e1 e2 = ECons (e1, e2)
let eif e1 e2 e3 = EIf (e1, e2, e3)
let elet binds e = ELet (binds, e)
let efun p e = EFun (p, e)
let eapp = return (fun e1 e2 -> EApp (e1, e2))
let ematch e cases = EMatch (e, cases)

(****************** Case ctors ******************)
let ccase p e = p, e

(****************** Binding ctors ******************)

let bbind isrec p e = isrec, p, e

(****************** Pat ctors ******************)

let pwild _ = PWild
let pvar id = PVar id
let pconst c = PConst c
let plist pl = PList pl
let ptuple pl = PTuple pl
let popcons = token "::" *> return (fun p1 p2 -> PCons (p1, p2))

(****************** Decl ctors ******************)

let dlet isrec p e = DLet (isrec, p, e)
let deff p te = DEffect (p, te)

(****************** Plain parsers ******************)

let cmp e1 e2 =
  let cmps =
    List.map
      (fun (sgn, op) -> lift2 op (e1 <* token sgn) e2)
      [ "=", eop Eq; "<", eop Less; "<=", eop Leq; ">", eop Gre; ">=", eop Geq ]
  in
  choice cmps
;;

let id_ check_fst =
  let check_inner c = check_fst c || is_digit c in
  satisfy check_fst
  >>= fun fst ->
  (match fst with
  | '_' -> take_while1
  | _ -> take_while)
    check_inner
  >>= function
  | _ as inner ->
    if is_keyword @@ Char.escaped fst ^ inner
    then fail "Keyword is reserved"
    else return @@ Char.escaped fst ^ inner
;;

let id =
  id_
  @@ function
  | 'a' .. 'z' | '_' -> true
  | _ -> false
;;

(****************** Const parsing ******************)

let uns = take_while1 is_digit <* ws >>= fun uns -> return @@ uns
let cunsint = uns >>= fun uns -> return @@ int_of_string uns >>| cint

let cint =
  option "" (token "+" <|> token "-")
  >>= fun sgn -> uns >>= fun uns -> return @@ int_of_string (sgn ^ uns) >>| cint
;;

let cbool =
  let _true = ttrue *> return (cbool true) in
  let _false = tfalse *> return (cbool false) in
  _true <|> _false
;;

let cstring =
  char '"'
  *> take_while (function
         | '"' -> false
         | _ -> true)
  <* char '"'
  >>| cstring
;;

let const = ws *> choice [ cint; cbool; cstring ] <* ws
let uns_const = ws *> choice [ cunsint; cbool; cstring ] <* ws

(****************** Pattern parsing ******************)

let pvar = id >>| pvar
let pwild = twild >>| pwild
let pconst = const >>| pconst

type pdispatch =
  { tuple : pdispatch -> pat t
  ; cons : pdispatch -> pat t
  ; pat : pdispatch -> pat t
  }

let pcons = return @@ fun p1 p2 -> PCons (p1, p2)

let pack =
  let pat d = fix @@ fun _self -> ws *> (d.tuple d <|> d.cons d) <* ws in
  let tuple d =
    fix
    @@ fun _self ->
    ws *> lift2 (fun hd tl -> hd :: tl) (d.cons d) (many1 (comma *> d.cons d))
    >>| ptuple
    <* ws
  in
  let cons d =
    fix
    @@ fun _self ->
    let plist = ws *> (between lsb rsb @@ sep_by semicol @@ d.pat d >>| plist) <* ws in
    let prim = ws *> choice [ pconst; pvar; pwild; plist; parens @@ d.pat d ] <* ws in
    ws *> chainr1 prim popcons <* ws
  in
  { tuple; cons; pat }
;;

let pat = pack.pat pack

(****************** Expr parsing ******************)

type edispatch =
  { key : edispatch -> exp t
  ; tuple : edispatch -> exp t
  ; exp : edispatch -> exp t
  ; op : edispatch -> exp t
  }

let efun args rhs = List.fold_right efun args rhs

let wthdebug p =
  p
  >>= fun res ->
  (pp_print_list pp_exp std_formatter) [ res ];
  return res
;;

let pack =
  let exp d = fix @@ fun _self -> ws *> (d.key d <|> d.tuple d <|> d.op d) <* ws in
  let key d =
    fix
    @@ fun _self ->
    let eif =
      ws *> lift3 eif (tif *> d.exp d) (tthen *> d.exp d) (telse *> d.exp d) <* ws
    in
    let elet =
      let binding =
        ws
        *> lift3
             bbind
             (tlet *> option false (trec >>| fun _ -> true))
             pat
             (lift2 efun (ws *> many pat <* token "=") (d.exp d <* tin))
        <* ws
      in
      ws *> lift2 elet (many1 binding) (d.exp d) <* ws
    in
    let efun = ws *> lift2 efun (tfun *> many pat <* tarrow) (d.exp d) <* ws in
    let ematch =
      let case = lift2 ccase (tbar *> pat <* tarrow) (d.exp d) in
      lift2 ematch (tmatch *> d.exp d <* twith) (many1 case)
    in
    peek_char_fail
    >>= function
    | 'l' -> elet
    | 'i' -> eif
    | 'f' -> efun
    | _ -> ematch
  in
  let tuple d =
    ws
    *> lift2
         (fun hd tl -> hd :: tl)
         (ws *> d.op d <* comma)
         (sep_by1 comma (d.op d <|> d.key d))
    >>| etuple
    <* ws
  in
  let op d =
    fix
    @@ fun _self ->
    let lst = ws *> (between lsb rsb @@ sep_by semicol (d.exp d)) <* ws in
    let prim =
      ws *> choice [ lst >>| elist; uns_const >>| econst; id >>| evar; parens @@ d.exp d ]
      <* ws
    in
    let app = chainl1 prim eapp in
    let mul =
      ws
      *> choice
           [ lift2 (eop Mul) (app <* token "*") (chainr1 (app <|> d.key d) mul); app ]
      <* ws
    in
    let add =
      let infop p =
        choice
          [ token "-" *> p >>| eunop Minus
          ; token "!" *> p >>| eunop Not
          ; token "+" *> p
          ; p
          ]
      in
      ws
      *> choice
           [ lift2
               (eop Add)
               (infop mul <* token "+")
               (chainr1 (infop mul <|> infop @@ d.key d) add)
           ; infop mul
           ]
      <* ws
    in
    let cons =
      ws
      *> choice
           [ lift2 econs (add <* token "::") (chainr1 (add <|> d.key d) eopcons); add ]
      <* ws
    in
    let cmp =
      ws
      *> choice
           [ lift2 (eop Less) (cons <* token "<") (chainr1 (cons <|> d.key d) less)
           ; cons
           ]
      <* ws
    in
    let and_ =
      ws
      *> choice
           [ lift2 (eop And) (cmp <* token "&&") (chainr1 (cmp <|> d.key d) _and); cmp ]
      <* ws
    in
    ws
    *> choice
         [ lift2 (eop Or) (cmp <* token "||") (chainr1 (and_ <|> d.key d) _or); and_ ]
    <* ws
  in
  { key; tuple; exp; op }
;;

let exp = pack.exp pack

(****************** Decl parsing ******************)

let decl =
  ws
  *> lift3
       dlet
       (tlet *> option false (trec >>| fun _ -> true))
       pat
       (lift2 efun (ws *> many pat <* token "=") exp)
  <* ws
;;

(****************** Decl parsing ******************)

let pprog (l : decl list) : prog = l

(****************** Prog parsing ******************)

let prog = many1 (skip *> decl <* option "" (token ";;") <* skip) >>| pprog

(****************** Tests ******************)
let test_exp_suc = parse_test_suc pp_exp exp
let test_pat_suc = parse_test_suc pp_pat pat
let test_prog_suc = parse_test_suc pp_prog prog

let%test _ =
  test_prog_suc
    {|
let fold init f lst = match lst with | [] -> acc | hd :: tl -> fold (f init hd) f tl
|}
  @@ [ DLet
         ( false
         , PVar "fold"
         , EFun
             ( PVar "init"
             , EFun
                 ( PVar "f"
                 , EFun
                     ( PVar "lst"
                     , EMatch
                         ( EVar "lst"
                         , [ PList [], EVar "acc"
                           ; ( PCons (PVar "hd", PVar "tl")
                             , EApp
                                 ( EApp
                                     ( EApp
                                         ( EVar "fold"
                                         , EApp (EApp (EVar "f", EVar "init"), EVar "hd")
                                         )
                                     , EVar "f" )
                                 , EVar "tl" ) )
                           ] ) ) ) ) )
     ]
;;

let%test _ =
  test_prog_suc
    {|
let rec fact n = match n with | 0 -> 1 | _ -> n * fact (n + -1)
|}
    [ DLet
        ( true
        , PVar "fact"
        , EFun
            ( PVar "n"
            , EMatch
                ( EVar "n"
                , [ PConst (CInt 0), EConst (CInt 1)
                  ; ( PWild
                    , EOp
                        ( Mul
                        , EVar "n"
                        , EApp
                            ( EVar "fact"
                            , EOp (Add, EVar "n", EUnOp (Minus, EConst (CInt 1))) ) ) )
                  ] ) ) )
    ]
;;

let%test _ =
  test_prog_suc
    {|
let a, b, (c, (d, e)) = 1, 2, (3, (4, 5));; let f _ = a + b + c + d + e;;
|}
    [ DLet
        ( false
        , PTuple
            [ PVar "a"; PVar "b"; PTuple [ PVar "c"; PTuple [ PVar "d"; PVar "e" ] ] ]
        , ETuple
            [ EConst (CInt 1)
            ; EConst (CInt 2)
            ; ETuple [ EConst (CInt 3); ETuple [ EConst (CInt 4); EConst (CInt 5) ] ]
            ] )
    ; DLet
        ( false
        , PVar "f"
        , EFun
            ( PWild
            , EOp
                ( Add
                , EVar "a"
                , EOp (Add, EVar "b", EOp (Add, EVar "c", EOp (Add, EVar "d", EVar "e")))
                ) ) )
    ]
;;

let%test _ =
  test_prog_suc "let map f l = match l with | [] -> [] | hd :: tl -> f hd :: map f tl"
  @@ [ DLet
         ( false
         , PVar "map"
         , EFun
             ( PVar "f"
             , EFun
                 ( PVar "l"
                 , EMatch
                     ( EVar "l"
                     , [ PList [], EList []
                       ; ( PCons (PVar "hd", PVar "tl")
                         , ECons
                             ( EApp (EVar "f", EVar "hd")
                             , EApp (EApp (EVar "map", EVar "f"), EVar "tl") ) )
                       ] ) ) ) )
     ]
;;

let%test _ =
  test_prog_suc "let x, y = 1 :: [2; 3], match z with | _ -> 4 :: 5 :: 6 :: rest;;"
  @@ [ DLet
         ( false
         , PTuple [ PVar "x"; PVar "y" ]
         , ETuple
             [ ECons (EConst (CInt 1), EList [ EConst (CInt 2); EConst (CInt 3) ])
             ; EMatch
                 ( EVar "z"
                 , [ ( PWild
                     , ECons
                         ( EConst (CInt 4)
                         , ECons (EConst (CInt 5), ECons (EConst (CInt 6), EVar "rest"))
                         ) )
                   ] )
             ] )
     ]
;;

let%test _ =
  test_prog_suc
    "let fib n = let rec helper fst snd n = match n with | 0 -> fst | 1 -> snd | _ -> \
     helper snd (fst + snd) (n + -1) in helper 0 1 n "
  @@ [ DLet
         ( false
         , PVar "fib"
         , EFun
             ( PVar "n"
             , ELet
                 ( [ ( true
                     , PVar "helper"
                     , EFun
                         ( PVar "fst"
                         , EFun
                             ( PVar "snd"
                             , EFun
                                 ( PVar "n"
                                 , EMatch
                                     ( EVar "n"
                                     , [ PConst (CInt 0), EVar "fst"
                                       ; PConst (CInt 1), EVar "snd"
                                       ; ( PWild
                                         , EApp
                                             ( EApp
                                                 ( EApp (EVar "helper", EVar "snd")
                                                 , EOp (Add, EVar "fst", EVar "snd") )
                                             , EOp
                                                 ( Add
                                                 , EVar "n"
                                                 , EUnOp (Minus, EConst (CInt 1)) ) ) )
                                       ] ) ) ) ) )
                   ]
                 , EApp
                     ( EApp (EApp (EVar "helper", EConst (CInt 0)), EConst (CInt 1))
                     , EVar "n" ) ) ) )
     ]
;;

(* let%test _ = test_exp_suc "let f x y = x + y in f 1 2" @@ EVar "" *)
