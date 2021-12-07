open C_lib.Ast
open C_lib.Parser
open Format
open C_lib.Interpreterctx

let test =
  parse
    prog
    {|
      #include <a.h>

      int main () {
        
        int *arr0 = malloc(sizeof(int) * 5);
        int ans0 = arr0;
        free(arr0);
        int *arr1 = malloc(sizeof(int) * 5);
        int ans1 = arr1;

        return (0);
      }
    |}
;;

let () =
  match test with
  | Ok prog ->
    (match prog with
    | C_PROG prg ->
      (match eval_d prg [ "ans0"; "ans1" ] with
      | Ok result -> print_string @@ result
      | Error msg -> print_string @@ msg)
    | other -> print_string @@ show_prog other)
  | Error _ -> print_string "syntax errorRRR"
;;
