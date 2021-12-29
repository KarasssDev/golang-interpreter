open Ast
open Parser

let test_parse ~label ~code ~expected =
  match parse prog code with
  | Error _ -> false
  | Result.Ok res when expected = res -> true
  | Result.Ok res ->
    let () =
      Printf.printf "[Parser test] %s failed.\nActual is:\n%s\n" label (show_prog res)
    in
    false
;;
