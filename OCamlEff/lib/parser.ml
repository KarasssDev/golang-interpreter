open Angstrom
open Ast

let parse p s = parse_string ~consume:All p s

let chainl1 e op =
  let rec go acc = lift2 (fun f x -> f acc x) op e >>= go <|> return acc in
  e >>= fun init -> go init

let rec chainr1 e op =
  e >>= fun a -> op >>= (fun f -> chainr1 e op >>| f a) <|> return a

let is_ws = function ' ' | '\t' -> true | _ -> false
let is_eol = function '\r' | '\n' -> true | _ -> false
let is_digit = function '0' .. '9' -> true | _ -> false


let is_keyword = function
  | "let" | "in" | "true" | "false" -> true
  | _ -> false

let ws = take_while is_ws

let eol = take_while is_eol

let token s = ws *> string s

let rp = token ")"
let lp = token "("
let parens p = lp *> p <* rp

let _in = token "in"
let _true = token "true"
let _false = token "false"
let _let = token "let"
let _eol = token "\n"

module Ctors = struct 
  let expr e = Expr e
  let arithop op e1 e2 = ArithOp (op, e1, e2)
  let boolop op e1 e2 = BoolOp (op, e1, e2)
  let letbind id e = LetBind (id, e)

  let letbindin id s e = LetBindIn (id, s, e)
  let var id = Var (id)
end

let _add = many1 (token "+") *> return (Ctors.arithop Add)
let _sub = token "-" *> return (Ctors.arithop Sub)
let _mul = token "*" *> return (Ctors.arithop Mul)
let _div = token "/" *> return (Ctors.arithop Div)

let _true = string "true" *> return True
let _false = string "false" *> return False

let identifier first_char_check = 
  let id_char_check = function 
    | 'a' .. 'z' | '0' .. '9' | '_' -> true 
    | _ -> false in
  ws *> peek_char
  >>= function 
    | Some c when first_char_check c -> (
      take_while id_char_check 
      >>= fun id ->
      match is_keyword id with true -> failwith "This id is reserved" | false -> return id
    )
    | _ -> fail "Invalid id"

let id = identifier (function 
  | 'a'..'z' | '_' -> true 
  | _ -> false
)

let number = 
  let sign = 
    peek_char
    >>= function
    | Some '-' -> advance 1 >>| fun () -> "-"
    | Some '+' -> advance 1 >>| fun () -> "+"
    | Some c when is_digit c -> return "+"
    | _ -> fail "Sign or digit expected" in
  ws *> sign 
  >>= fun sign -> take_while1 is_digit
  >>= fun uns -> return (Number (Int (int_of_string (sign ^ uns))))

  let factop = _mul <|> _div <?> "'*' or '/' or '%' expected" <* ws
  let termop = ws *> _add <|> _sub <?> "'+' or '-' expected" <* ws
;;


let prog = 
  fix (fun prog ->
    let expr = 
      fix (fun expr ->
        let factor = number <|> parens expr in 
        let term = chainl1 factor factop in 
        chainl1 term termop) in 
    let stmt = 
      fix (fun stmt ->
        let exprstmt = expr >>= fun e -> return (Ctors.expr e) in

        let letbnd = _let *> id 
        >>= fun id -> token "=" *> exprstmt
        >>= fun s -> return (Ctors.letbind id s)


        in letbnd <|> exprstmt)
  in eol *> sep_by eol stmt <* eol) 
;;