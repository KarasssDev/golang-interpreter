open Angstrom
open Ast
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
let ( >=> ) p1 p2 = many1 p1 >>= fun lhs -> p2 >>= fun rhs -> return @@ lhs @ rhs
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

let is_keyword = function
  | "let"
  | "in"
  | "true"
  | "false"
  | "rec"
  | "fun"
  | "perform"
  | "continue"
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
let parens = between lp rp

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
let eunop o e = EUnOp (o, e)
let evar id = EVar id
let elist l = EList l
let etuple l = ETuple l
let eif e1 e2 e3 = EIf (e1, e2, e3)
let elet binds e = ELet (binds, e)
let efun p e = EFun (p, e)
let eapp e1 e2 = EApp (e1, e2)
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

(****************** Decl ctors ******************)

let dlet isrec p e = DLet (isrec, p, e)
let deff p te = DEffect (p, te)

(****************** Plain parsers ******************)

let choice_op ops =
  let trans (tok, f) = token tok *> ws *> return f in
  choice @@ List.map trans ops
;;

let factop = choice_op [ "*", eop Mul; "/", eop Div ]
let unop = choice_op [ "-", eunop Minus; "!", eunop Not ]
let termop = choice_op [ "+", eop Add; "-", eop Sub ]
let cmpop = choice_op [ ">=", eop Geq; ">", eop Gre; "<=", eop Leq; "<", eop Less ]
let eqneqop = choice_op [ "=", eop Eq; "<>", eop Neq ]
let andor = choice_op [ "&&", eop And; "||", eop Or ]

let id =
  let check_fst = function
    | 'a' .. 'z' | '_' -> true
    | _ -> false
  in
  let check_inner c = check_fst c || is_digit c in
  satisfy check_fst
  >>= fun fst ->
  (match fst with
  | '_' -> take_while1
  | _ -> take_while)
    check_inner
  >>= function
  | _ as inner ->
    if is_keyword inner
    then failwith "Keyword is reserved"
    else return (Char.escaped fst ^ inner)
;;

(****************** Const parsing ******************)

let cint =
  let sign =
    peek_char
    >>= function
    | Some '-' -> advance 1 >>| fun () -> "-"
    | Some '+' -> advance 1 >>| fun () -> "+"
    | Some c when is_digit c -> return "+"
    | _ -> fail "Sign or digit expected"
  in
  ws *> sign
  <* ws
  >>= fun sign ->
  take_while1 is_digit <* ws >>= fun uns -> return @@ int_of_string (sign ^ uns) >>| cint
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
let test_const_suc = parse_test_suc pp_const const
let test_const_fail = parse_test_fail pp_const const

let%test _ = test_const_suc {| "he1+l__lo"  |} @@ CString "he1+l__lo"
let%test _ = test_const_suc "- 123  " @@ CInt (-123)
let%test _ = test_const_suc " true " @@ CBool true
let%test _ = test_const_suc "false " @@ CBool false
let%test _ = test_const_fail "falsee "
let%test _ = test_const_fail "-4 2 "
let%test _ = test_const_fail " \"some"

(****************** Pattern parsing ******************)

let pvar = id >>| pvar
let pwild = twild >>| pwild
let pconst = const >>| pconst
let pprimitive = choice [ pconst; pvar; pwild ]

let pat =
  fix
  @@ fun pat ->
  let plist =
    let plistbr = between lsb rsb (sep_by1 semicol pat <|> return []) >>| plist in
    let plistcons =
      choice [ between lp rp pat; plistbr; pprimitive ]
      <* tlistcons
      >=> (plistbr
          <|> pwild
          >>| function
          | PList l -> l
          | _ as rhs -> [ rhs ])
      >>| plist
    in
    plistcons <|> plistbr
  in
  let ptuple =
    let tuplemember = choice [ between lp rp pat; plist; pprimitive ] in
    tuplemember <* comma <* ws >=> (tuplemember >>| mklist) >>| ptuple
  in
  ws *> choice [ ptuple; plist; pprimitive; between lp rp pat ] <* ws
;;

let test_pat_suc = parse_test_suc pp_pat pat
let test_pat_fail = parse_test_fail pp_pat pat

let%test _ = test_pat_suc "[a; f]" @@ PList [ PVar "a"; PVar "f" ]
let%test _ = test_pat_suc {|"some_string"|} @@ PConst (CString "some_string")
let%test _ = test_pat_suc "_ :: []" @@ PList [ PWild ]
let%test _ = test_pat_suc "[[[1]]]" @@ PList [ PList [ PList [ PConst (CInt 1) ] ] ]

let%test _ =
  test_pat_suc
    "[[1]; 2 :: []]"
    (PList [ PList [ PConst (CInt 1) ]; PList [ PConst (CInt 2) ] ])
;;

let%test _ = test_pat_suc "true :: _" @@ PList [ PConst (CBool true); PWild ]
let%test _ = test_pat_suc "_, a" @@ PTuple [ PWild; PVar "a" ]
let%test _ = test_pat_suc "(a), (b)" @@ PTuple [ PVar "a"; PVar "b" ]
let%test _ = test_pat_suc "(((a), (b)))" @@ PTuple [ PVar "a"; PVar "b" ]
let%test _ = test_pat_suc "((((a))))" @@ PVar "a"

let%test _ =
  test_pat_suc "(1, 2) :: []" @@ PList [ PTuple [ PConst (CInt 1); PConst (CInt 2) ] ]
;;

let%test _ =
  test_pat_suc "a, (b, c, (d, e)), (((f)))"
  @@ PTuple
       [ PVar "a"
       ; PTuple [ PVar "b"; PVar "c"; PTuple [ PVar "d"; PVar "e" ] ]
       ; PVar "f"
       ]
;;

let%test _ =
  test_pat_suc "((1), (((2)))) :: [(3, 4)]"
  @@ PList
       [ PTuple [ PConst (CInt 1); PConst (CInt 2) ]
       ; PTuple [ PConst (CInt 3); PConst (CInt 4) ]
       ]
;;

(****************** Expr parsing ******************)

let exp =
  fix
  @@ fun exp ->
  let econst = const >>| econst in
  let evar = id >>| evar in
  let eop =
    let factor =
      let facmember = [ parens exp; econst; evar ] in
      let unopmember = List.map (fun p -> unop <*> p) facmember in
      choice unopmember <|> choice facmember
    in
    let term = chainl1 factor factop in
    let expr = chainl1 term termop in
    let comp = chainl1 expr cmpop in
    let equneq = chainl1 comp eqneqop in
    chainl1 equneq andor
  in
  let eif = lift3 eif (tif *> exp) (tthen *> exp) (telse *> exp) in
  let ematch =
    lift2
      ematch
      (tmatch *> exp)
      (twith *> many1 (lift2 ccase (tbar *> pat) (tarrow *> exp)))
  in
  let elet =
    let binding =
      lift3
        bbind
        (tlet *> option false (trec >>| fun _ -> true))
        (pat <* token "=")
        (exp <* tin)
    in
    lift2 elet (many1 binding) exp
  in
  let efun = lift2 efun (tfun *> pat) (tarrow *> exp) in
  ws *> choice [ efun; elet; ematch; eif; parens exp; eop; evar; econst ]
;;

let test_exp_suc = parse_test_suc pp_exp exp
let test_exp_fail = parse_test_fail pp_exp exp

let%test _ =
  test_exp_suc "let pl = 1 in fun x,y -> x - pl + y"
  @@ ELet
       ( [ false, PVar "pl", EConst (CInt 1) ]
       , EFun
           ( PTuple [ PVar "x"; PVar "y" ]
           , EOp (Add, EOp (Sub, EVar "x", EVar "pl"), EVar "y") ) )
;;

let%test _ =
  test_exp_suc "let x = 1 in let y = 2 in 1 + 2"
  @@ ELet
       ( [ false, PVar "x", EConst (CInt 1); false, PVar "y", EConst (CInt 2) ]
       , EOp (Add, EConst (CInt 1), EConst (CInt 2)) )
;;

let%test _ =
  test_exp_suc "match x with | a :: [] -> a | _ -> 0"
  @@ EMatch (EVar "x", [ PList [ PVar "a" ], EVar "a"; PWild, EConst (CInt 0) ])
;;

let%test _ =
  test_exp_suc "match x + 1 > y / 2 with | true -> x + 1 | false -> x - 2"
  @@ EMatch
       ( EOp
           ( Gre
           , EOp (Add, EVar "x", EConst (CInt 1))
           , EOp (Div, EVar "y", EConst (CInt 2)) )
       , [ PConst (CBool true), EOp (Add, EVar "x", EConst (CInt 1))
         ; PConst (CBool false), EOp (Sub, EVar "x", EConst (CInt 2))
         ] )
;;

let%test _ =
  test_exp_suc "if x + 20 <= 30 then true else false"
  @@ EIf
       ( EOp (Leq, EOp (Add, EVar "x", EConst (CInt 20)), EConst (CInt 30))
       , EConst (CBool true)
       , EConst (CBool false) )
;;

let%test _ =
  test_exp_suc "true = false || 1=1"
  @@ EOp
       ( Or
       , EOp (Eq, EConst (CBool true), EConst (CBool false))
       , EOp (Eq, EConst (CInt 1), EConst (CInt 1)) )
;;

let%test _ =
  test_exp_suc "(((-(-(-(+1))))))"
  @@ EUnOp (Minus, EUnOp (Minus, EUnOp (Minus, EConst (CInt 1))))
;;

let%test _ =
  test_exp_suc " - sk+ 8*f- (- 9 )"
  @@ EOp
       ( Sub
       , EOp (Add, EUnOp (Minus, EVar "sk"), EOp (Mul, EConst (CInt 8), EVar "f"))
       , EUnOp (Minus, EConst (CInt 9)) )
;;