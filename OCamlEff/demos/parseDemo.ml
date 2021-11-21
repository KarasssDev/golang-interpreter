open OcamlEff_lib.Ast
open OcamlEff_lib.Parser
open Format

let test = parse prog {|

-(5 + 3)


|}

let () =
  match test with
  | Ok prog ->
    pp_print_list pp_stmt std_formatter prog;
    print_newline ()
  | Error _ -> printf "syntax error";;
