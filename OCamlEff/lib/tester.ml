open Ast
open Parser

let test_parse ~label ~code ~expected =
  match parse prog code with
  | Error _ -> false
  | Result.Ok res when expected = res ->
    let () = Printf.printf "Test %s passed!\n" label in
    true
  | Result.Ok res ->
    let () = Printf.printf "Test %s failed.\nActual is:\n%s\n" label (show_prog res) in
    false
;;
