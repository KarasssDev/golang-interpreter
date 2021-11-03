open OcamlEff_lib.Ast
open OcamlEff_lib.Parser
open Format

let test = parse prog {|

let bebra = 6 in
  let kek = 4


|}


let () =
  match test with
  | Ok prog -> (
    pp_print_list pp_stmt std_formatter prog;
    print_newline()
  )
  | Error _ -> printf "syntax error"