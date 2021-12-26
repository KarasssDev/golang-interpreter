open Ast
open Format
open Parser
open Typing

let test_parse s expected =
  match parse prog s with
  | Error _ -> false
  | Result.Ok res when expected = res -> true
  | Result.Ok res ->
    print_string "Actual is:\n";
    pp_prog std_formatter res;
    false
;;

let test_typing s expected =
  match parse exp s with
  | Error _ ->
    Printf.printf "Parse error";
    false
  | Result.Ok tree ->
    (match w tree with
    | Error _ ->
      Printf.printf "Typing error";
      false
    | Result.Ok res when expected = res -> true
    | Result.Ok res ->
      print_string "Actual is: \n";
      pp_tyexp std_formatter res;
      false)
;;
