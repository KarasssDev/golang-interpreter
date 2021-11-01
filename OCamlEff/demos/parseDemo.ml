open OcamlEff_lib.Ast
open OcamlEff_lib.Parser
open Format

let test = parse prog {|

let bebra = 22 + 3

let nasvay = 228 + 1337
let kek = 0


|}


let () =
  match test with
  | Ok prog -> (
    pp_print_list pp_stmt std_formatter prog;
    print_newline()
  )
  | Error _ -> printf "syntax error"