open OcamlEff_lib.Eval
open Format

let _ =
  let () = Printf.printf "Exception imitation\n\n" in
  eval_pp
    ~code:
      {|

      effect EmptyListException : int
      ;;

      let list_hd = function 
      | [] -> perform EmptyListException
      | hd :: _ -> hd
      ;;

      let empty = [];;
      let non_empty = [1; 2; 3];;

      let safe_list_hd l = match list_hd l with 
      | effect EmptyListException k -> 0, false 
      | res -> res, true
      ;;

      let empty_hd = safe_list_hd empty;;
      let non_empty_hd = safe_list_hd non_empty;;

    |}
;;
