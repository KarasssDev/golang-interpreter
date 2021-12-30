open OcamlEff_lib.Eval
open Format

let _ =
  let () = Printf.printf "Fixpoint test\n\n" in
  test
    ~code:
      {|

      let rec fix f x = f (fix f) x;;

      let f self n = if n <= 1 then n else self (n - 1) * n;;

      let fact10 = fix f 10
    |}
;;
