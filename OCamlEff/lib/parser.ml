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

let is_ws = function
  | ' ' | '\t' -> true
  | _ -> false
;;

let chainl1 e op =
  let rec go acc = lift2 (fun f x -> f acc x) op e >>= go <|> return acc in
  e >>= fun init -> go init
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
  pl >>= fun init -> go init
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
  | "effect"
  | "match" -> true
  | _ -> false
;;

let ws = take_while is_ws
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

let eop o e1 e2 = EOp (o, e1, e2)
let add_ = token "+" *> (return @@ eop Add)
let sub_ = token "-" *> (return @@ eop Sub)
let mul_ = token "*" *> (return @@ eop Mul)
let div_ = token "/" *> (return @@ eop Div)
let eq_ = token "=" *> (return @@ eop Eq)
let less_ = token "<" *> (return @@ eop Less)
let gre_ = token ">" *> (return @@ eop Gre)
let leq_ = token "<=" *> (return @@ eop Leq)
let geq_ = token ">=" *> (return @@ eop Geq)
let and_ = token "&&" *> (return @@ eop And)
let or_ = token "||" *> (return @@ eop Or)
let cons_ = token "::" *> return econs

let app_unop p =
  choice
    [ token "-" *> p >>| eunop Minus; token "!" *> p >>| eunop Not; token "+" *> p; p ]
;;

let id_ check_fst =
  let check_inner c = check_fst c || is_digit c in
  ws *> satisfy check_fst
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
    choice [ elet; eif; efun; ematch ]
  in
  let tuple d =
    lift2 ( @ ) (many1 (d.op d <* comma)) (d.op d <|> d.key d >>| fun rhs -> [ rhs ])
    >>| etuple
  in
  let op d =
    fix
    @@ fun _self ->
    let lst = ws *> (between lsb rsb @@ sep_by semicol (d.exp d)) <* ws in
    let prim =
      ws *> choice [ lst >>| elist; uns_const >>| econst; id >>| evar; parens @@ d.exp d ]
      <* ws
    in
    let app = ws *> chainl1 prim eapp <* ws in
    let mul = procl (mul_ <|> div_) app @@ d.key d in
    let add = procl (add_ <|> sub_) (app_unop mul) (app_unop @@ d.key d) in
    let cons = procr cons_ add @@ d.key d in
    let cmp = procl (leq_ <|> less_ <|> geq_ <|> gre_) cons @@ d.key d in
    let eq = procl eq_ cmp @@ d.key d in
    let _and = procl and_ eq @@ d.key d in
    ws *> (procl or_ _and @@ d.key d) <* ws
  in
  { key; tuple; exp; op }
;;

let exp = pack.exp pack

(****************** Type parsing ******************)

let tyexp =
  fix
  @@ fun tyexp ->
  let prim =
    ws
    *> (twild *> return TWild
       <|> token "int" *> return TInt
       <|> token "string" *> return TString
       <|> token "bool" *> return TBool
       <|> (uns >>| fun bind -> TVar (int_of_string bind))
       <|> parens tyexp)
    <* ws
  in
  let list =
    prim
    >>= fun ty ->
    many1 @@ (ws *> token "list")
    >>= fun l ->
    let rec wrap acc n =
      match n with
      | 0 -> acc
      | _ -> wrap (TList acc) (n - 1)
    in
    return @@ wrap ty (List.length l)
  in
  let tup =
    sep_by1 (token "*" *> ws) (list <|> prim)
    >>| function
    | [ a ] -> a
    | tup -> TTuple tup
  in
  ws *> chainr1 tup (tarrow *> return (fun t1 t2 -> TArrow (t1, t2))) <* ws
;;

(****************** Decl parsing ******************)

let decl =
  let dlet =
    lift3
      dlet
      (tlet *> option false (trec >>| fun _ -> true))
      pat
      (lift2 efun (ws *> many pat <* token "=") exp)
  in
  let deff =
    let id =
      id_
      @@ function
      | 'a' .. 'z' | 'A' .. 'Z' -> true
      | _ -> false
    in
    lift2 deff (token "effect" *> id <* token ":") tyexp
  in
  ws *> (deff <|> dlet) <* ws
;;

(****************** Prog parsing ******************)

let pprog (l : decl list) : prog = l
let prog = many1 (skip *> decl <* option "" (token ";;") <* skip) >>| pprog

(****************** Tests ******************)
let test_exp_suc = parse_test_suc pp_exp exp
let test_pat_suc = parse_test_suc pp_pat pat
let test_prog_suc = parse_test_suc pp_prog prog
let test_tyexp_suc = parse_test_suc pp_tyexp tyexp

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

let%test _ =
  test_prog_suc
    "let reverse = let rec helper acc l = match l with | [] -> acc | hd :: tl -> helper \
     tl (hd :: acc) in helper []"
  @@ [ DLet
         ( false
         , PVar "reverse"
         , ELet
             ( [ ( true
                 , PVar "helper"
                 , EFun
                     ( PVar "acc"
                     , EFun
                         ( PVar "l"
                         , EMatch
                             ( EVar "l"
                             , [ PList [], EVar "acc"
                               ; ( PCons (PVar "hd", PVar "tl")
                                 , EApp
                                     ( EApp (EVar "helper", EVar "tl")
                                     , ECons (EVar "hd", EVar "acc") ) )
                               ] ) ) ) )
               ]
             , EApp (EVar "helper", EList []) ) )
     ]
;;

let%test _ =
  test_exp_suc "1 + f x < (fun x -> g x y) = true || 1=0"
  @@ EOp
       ( Or
       , EOp
           ( Eq
           , EOp
               ( Less
               , EOp (Add, EConst (CInt 1), EApp (EVar "f", EVar "x"))
               , EFun (PVar "x", EApp (EApp (EVar "g", EVar "x"), EVar "y")) )
           , EConst (CBool true) )
       , EOp (Eq, EConst (CInt 1), EConst (CInt 0)) )
;;

let%test _ =
  test_prog_suc
    "let rec all predicate list = match list with | [] -> true | hd :: tl -> if \
     !predicate hd then false else all predicate tl"
  @@ [ DLet
         ( true
         , PVar "all"
         , EFun
             ( PVar "predicate"
             , EFun
                 ( PVar "list"
                 , EMatch
                     ( EVar "list"
                     , [ PList [], EConst (CBool true)
                       ; ( PCons (PVar "hd", PVar "tl")
                         , EIf
                             ( EUnOp (Not, EApp (EVar "predicate", EVar "hd"))
                             , EConst (CBool false)
                             , EApp (EApp (EVar "all", EVar "predicate"), EVar "tl") ) )
                       ] ) ) ) )
     ]
;;

let%test _ =
  test_tyexp_suc "_ * int -> (int list list -> bool -> string) -> 1 list"
  @@ TArrow
       ( TTuple [ TWild; TInt ]
       , TArrow (TArrow (TList (TList TInt), TArrow (TBool, TString)), TList (TVar 1)) )
;;

let%test _ =
  test_prog_suc "effect Choice : string -> int;; let f x y = f (x y)"
  @@ [ DEffect ("Choice", TArrow (TString, TInt))
     ; DLet
         ( false
         , PVar "f"
         , EFun (PVar "x", EFun (PVar "y", EApp (EVar "f", EApp (EVar "x", EVar "y")))) )
     ]
;;
