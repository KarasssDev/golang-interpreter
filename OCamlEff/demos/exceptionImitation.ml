open OcamlEff_lib.Eval

let _ =
  let code = Stdio.In_channel.input_all Caml.stdin in
  eval_pp ~code
;;
