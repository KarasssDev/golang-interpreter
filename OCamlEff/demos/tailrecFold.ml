open OcamlEff_lib.Eval

let _ =
  let () = Printf.printf "Tailrec fold test\n\n" in
  eval_pp
    ~code:
      {|

      let rec fold f init = function 
        | [] -> init 
        | hd :: tl -> fold f (f init hd) tl
      ;;

      let sum = fold (fun x y -> x + y) 0
      ;;

      let sum_of_first_ten = sum [1; 2; 3; 4; 5; 6; 7; 8; 9; 10]
    |}
;;
