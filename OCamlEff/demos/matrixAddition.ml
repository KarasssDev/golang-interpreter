open OcamlEff_lib.Eval
open Format

let _ =
  let () = Printf.printf "Matrix addition test\n\n" in
  eval_pp
    ~code:
      {|

      let mtx1 = [[1; 2; 3; 4];
                  [1; 2; 3; 4];
                  [1; 2; 3; 4]];;

      let mtx2 = [[0; 1; 0; 8];
                  [0; 0; 1; 3];
                  [1; 0; 1; 2]];;

      let rec sum_up_row = function 
      | [], [] -> []
      | hd1 :: tl1, hd2 :: tl2 -> (hd1 + hd2) :: sum_up_row (tl1, tl2)
      ;;

      let rec sum_up_matrix = function
      | [], [] -> []
      | hd1 :: tl1, hd2 :: tl2 -> (sum_up_row (hd1, hd2)) :: sum_up_matrix (tl1, tl2)
      ;;

      let mtx3 = sum_up_matrix (mtx1, mtx2)
    |}
;;
