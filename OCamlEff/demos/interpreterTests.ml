open OcamlEff_lib.Eval

let _ =
  let code = Stdio.In_channel.input_all Caml.stdin in
  let () = eval_pp ~code in
  Printf.printf "=====================================\n"
;;
