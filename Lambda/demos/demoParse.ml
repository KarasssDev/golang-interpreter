open Lambda_lib

let () =
  let s = Stdio.In_channel.input_all Caml.stdin in
  match Lambda_lib.Parser.parse s with
  | Result.Ok ast -> Format.printf "%a\n%!" (Printast.pp Format.pp_print_char) ast
  | Error _ -> Format.printf "Some error"
;;
