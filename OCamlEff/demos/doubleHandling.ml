open OcamlEff_lib.Eval

let _ =
  let () = Printf.printf "Double handling test\n\n" in
  eval_pp
    ~code:
      {|

      effect E: int -> int;;

      let helper x = match perform (E x) with
      | effect (E s) k -> continue k (s*s)
      | l -> l
      ;;

      let res = match perform (E 5) with
      | effect (E s) k -> continue k (s*s)
      | l -> helper l;;
   |}
;;
