open OcamlEff_lib.Ast
open OcamlEff_lib.Parser
open Format

let test = parse expr "8 - 7**(3 + 5)"

let () =
  match test with
  | Ok expr -> pp_print_list pp_expr std_formatter [expr]
  | Error _ -> printf "syntax error"