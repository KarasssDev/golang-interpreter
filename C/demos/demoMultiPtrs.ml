open C_lib.Ast
open C_lib.Parser
open Format
open C_lib.Interpreterctx

let test =
  parse prog
    {|
      #include <a.h>

      int main () {
        
        int** arr = malloc(sizeof(int) * 2);

        for (int i = 0; i < 2; i++) {
          arr[i] = malloc(sizeof(int) * 3);
        }

        for (int i = 0; i < 2; i++) {
          for (int j = 0; j < 3; j++) {
            if (i == 1) {
              *(*(arr + i) + j) = 2 * j;
            } else {
              *(*(arr + i) + j) = j;
            } 
          }
        }

        int ans00 = *(*(arr + 0) + 0);
        int ans01 = *(*(arr + 0) + 1);
        int ans02 = *(*(arr + 0) + 2);

        int ans10 = *(*(arr + 1) + 0);
        int ans11 = *(*(arr + 1) + 1);
        int ans12 = *(*(arr + 1) + 2);

        return (0);
      }
      
    |}

let () =
  match test with
  | Ok prog -> (
      match prog with
      | C_PROG prg -> (
          match
            eval_d prg [ "ans00"; "ans01"; "ans02"; "ans10"; "ans11"; "ans12" ]
          with
          | Ok result -> print_string @@ result
          | Error msg -> print_string @@ msg)
      | other -> print_string @@ show_prog other)
  | Error _ -> print_string "syntax errorRRR"
