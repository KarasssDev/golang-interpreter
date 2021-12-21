open C_lib.Ast
open C_lib.Parser
open Format
open C_lib.Interpreterctx

let test =
  parse prog
    {|
      
      #include <a.h>
      
      int factorial (int n) {  
        if (n == 0) {  
          return 1;
        }  
        else {
          return(n * factorial(n - 1));
        }
      }  

      int main () {

        int ans0 = factorial(0);
        int ans1 = factorial(1);
        int ans2 = factorial(2);
        int ans3 = factorial(3);
        int ans4 = factorial(4);
        int ans5 = factorial(5);

        return (0);
      }

      
    |}

let () =
  match test with
  | Ok prog -> (
      match prog with
      | C_PROG prg -> (
          match
            eval_d prg [ "ans0"; "ans1"; "ans2"; "ans3"; "ans4"; "ans5" ]
          with
          | Ok result -> print_string result
          | Error msg -> print_string msg)
      | other -> print_string @@ show_prog other)
  | Error _ -> print_string "syntax errorRRR"
