open OcamlEff_lib.Ast
open OcamlEff_lib.Parser
open Format

let test = parse const "- 123 "

let () =
  match test with
  | Ok const ->
    pp_print_list pp_const std_formatter [ const ];
    print_newline ()
  | Error _ -> printf "syntax error\n"
;;
