open Ast

let rec pp ppf = function
  | Var c -> Format.fprintf ppf "%c" c
  | App (l, r) -> Format.fprintf ppf "(%a %a)" pp l pp r
  (*
    | App (l, r) ->
        Format.fprintf ppf "%a %a" pp l pp r (* Buggy implementation *)
        *)
  | Abs (x, b) -> Format.fprintf ppf "(\\%c . %a)" x pp b
