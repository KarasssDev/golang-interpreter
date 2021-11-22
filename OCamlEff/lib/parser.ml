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
let eol = take_while is_eol
let token s = ws *> string s
let rp = token ")"
let lp = token "("
let rsb = token "]"
let lsb = token "["
let comma = token ","
let semicol = token ";"
let between l r p = l *> p <* r

(****************** Tokens ******************)
let tin = token "in"
let ttrue = token "true"
let tfalse = token "false"
let tlet = token "let"
let teol = token "\n"
let twild = token "_"

(****************** Const ctors ******************)

let cint n = CInt n
let cbool b = CBool b
let cstring s = CString s

(****************** Exp ctors ******************)

let econst c = EConst c
let eop o e1 e2 = EOp (o, e1, e2)
let evar id = EVar id
let elist l = EList l
let etuple l = ETutple l
let eif e1 e2 e3 = EIf (e1, e2, e3)
let elet inn out = ELet (inn, out)
let eletrec inn out = ELetRec (inn, out)
let efun p e = EFun (p, e)
let eapp e1 e2 = EApp (e1, e2)
let ematch e cases = EMatch (e, cases)

(****************** Pat ctors ******************)

let pwild _ = PWild
let pvar id = PVar id
let pconst c = PConst c
let plist pl = PList pl
let ptuple pl = PTuple pl

(****************** Decl ctors ******************)

let dlet p e = DLet (p, e)
let dletrec p e = DLetRec (p, e)
let deff p te = DEffect (p, te)

(****************** Plain parsers ******************)

let _add = token "+" *> return (eop Add)
let _sub = token "-" *> return (eop Sub)
let _mul = token "*" *> return (eop Mul)
let _div = token "/" *> return (eop Div)

let _id =
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

let _cint =
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
  take_while1 is_digit <* ws >>= fun uns -> return (int_of_string (sign ^ uns)) >>| cint
;;

let _cbool =
  let _true = ttrue *> return (cbool true) in
  let _false = tfalse *> return (cbool false) in
  _true <|> _false
;;

let _cstring =
  char '"'
  *> take_while (function
         | '"' -> false
         | _ -> true)
  <* char '"'
  >>| cstring
;;

let const = ws *> choice [ _cint; _cbool; _cstring ] <* ws
let test_const_suc = parse_test_suc pp_const const
let test_const_fail = parse_test_fail pp_const const

let%test _ = test_const_suc {| "he1+l__lo"  |} (CString "he1+l__lo")
let%test _ = test_const_suc "- 123  " (CInt (-123))
let%test _ = test_const_suc " true " (CBool true)
let%test _ = test_const_suc "false " (CBool false)
let%test _ = test_const_fail "falsee "
let%test _ = test_const_fail "-4 2 "
let%test _ = test_const_fail " \"some"

(****************** Pattern parsing ******************)

let _pvar = _id >>| pvar
let _pwild = twild >>| pwild
let _pconst = const >>| pconst
let _pprimitive = choice [ _pconst; _pvar; _pwild ]

let pat =
  fix (fun pat ->
      let _plistbr = lsb *> (sep_by1 semicol pat <|> return []) <* rsb >>| plist in
      let _plistcons =
        many1 (choice [ lp *> pat <* rp; _plistbr; _pprimitive ] <* token "::")
        >>= fun lhs ->
        _plistbr
        <|> _pwild
        >>= fun rhs ->
        return
          (match rhs with
          | PList l -> lhs @ l
          | _ -> lhs @ [ rhs ])
        >>| plist
      in
      ws *> choice [ _plistcons; _plistbr; _pprimitive ] <* ws)
;;

let test_pat_suc = parse_test_suc pp_pat pat
let test_pat_fail = parse_test_fail pp_pat pat

let%test _ = test_pat_suc "[a; f]" (PList [ PVar "a"; PVar "f" ])
let%test _ = test_pat_suc {|"some_string"|} (PConst (CString "some_string"))
let%test _ = test_pat_suc "_ :: []" (PList [ PWild ])
let%test _ = test_pat_suc "[[[1]]]" (PList [ PList [ PList [ PConst (CInt 1) ] ] ])

let%test _ =
  test_pat_suc
    "[[1]; 2 :: []]"
    (PList [ PList [ PConst (CInt 1) ]; PList [ PConst (CInt 2) ] ])
;;

let%test _ = test_pat_suc "true :: _" (PList [ PConst (CBool true); PWild ])
