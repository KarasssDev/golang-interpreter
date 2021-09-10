(* TODO: implement parser here *)
open Angstrom

let is_space = function ' ' | '\t' -> true | _ -> false
let spaces = skip_while is_space
let varname = satisfy (function 'a' .. 'z' -> true | _ -> false)

let conde = function
  | [] -> fail "empty conde"
  | h :: tl -> List.fold_left ( <|> ) h tl

type dispatch =
  { apps: dispatch -> char Ast.t Angstrom.t
  ; single: dispatch -> char Ast.t Angstrom.t }

let parse_lam =
  let single pack =
    fix (fun _ ->
        conde
          [ char '(' *> pack.apps pack <* char ')'
          ; ( (string "λ" <|> string "\\") *> spaces *> varname
            <* spaces <* char '.'
            >>= fun var -> pack.apps pack >>= fun b -> return (Ast.Abs (var, b))
            ); (varname <* spaces >>= fun c -> return (Ast.Var c)) ] ) in
  let apps pack =
    many1 (spaces *> pack.single pack <* spaces)
    >>= function
    | [] -> fail "bad syntax"
    | x :: xs -> return @@ List.fold_left (fun l r -> Ast.App (l, r)) x xs in
  {single; apps}

let parse =
  Angstrom.parse_string (parse_lam.apps parse_lam) ~consume:Angstrom.Consume.All

let parse_optimistically str = Result.get_ok (parse str)

let%expect_test _ =
  Format.printf "%a" Printast.pp (parse_optimistically "x y");
  [%expect {| App (Var (x), Var (y)) |}]

let%expect_test _ =
  Format.printf "%a" Printast.pp (parse_optimistically "(x y)");
  [%expect {| App (Var (x), Var (y)) |}]

let%expect_test _ =
  Format.printf "%a" Printast.pp (parse_optimistically "(\\x . x x)");
  [%expect {| Abs (x, App (Var (x), Var (x))) |}]

let%expect_test _ =
  Format.printf "%a" Printast.pp (parse_optimistically "(λf.λx. f (x x))");
  [%expect {| Abs (f, Abs (x, App (Var (f), App (Var (x), Var (x))))) |}]
