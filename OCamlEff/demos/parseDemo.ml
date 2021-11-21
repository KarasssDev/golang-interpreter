open OcamlEff_lib.Ast
open OcamlEff_lib.Parser
open Format

let test = parse pat "[_; 2; [[_]; (1, 2, (3, 4))]] "

let () =
  match test with
  | Ok pat ->
    pp_print_list pp_pat std_formatter [pat];
    print_newline ()
  | Error _ -> printf "syntax error\n";;
