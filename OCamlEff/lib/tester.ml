open Ast
open Format
open Parser

let test_parse s expected =
  match parse prog s with
  | Error _ -> false
  | Result.Ok res ->
      if expected = res then true
      else (
        print_string "Actual is:\n";
        pp_prog std_formatter res;
        false )
