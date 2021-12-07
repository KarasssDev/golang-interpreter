open C_lib.Ast
open C_lib.Parser
open Format
open C_lib.Interpreterctx

let test =
  parse
    prog
    {|
      
      #include <a.h>

      int fib(int n) {
          if (n <= 1) {
            return n;
          }
          return (fib(n-1) + fib(n-2));
      }


      int main () {
      
        int ans0 = fib(0);
        int ans1 = fib(1);
        int ans2 = fib(2);
        int ans3 = fib(3);
        int ans4 = fib(4);
        int ans5 = fib(5);
        int ans6 = fib(6);
        int ans7 = fib(7);
        int ans8 = fib(8);
        int ans9 = fib(9);
        int ans10 = fib(10);

        return (1);
      }
      
    |}
;;

let () =
  match test with
  | Ok prog ->
    (match prog with
    | C_PROG prg ->
      (match
         eval_d
           prg
           [ "ans0"
           ; "ans1"
           ; "ans2"
           ; "ans3"
           ; "ans4"
           ; "ans5"
           ; "ans6"
           ; "ans7"
           ; "ans8"
           ; "ans9"
           ; "ans10"
           ]
       with
      | Ok result -> print_string @@ result
      | Error msg -> print_string @@ msg)
    | other -> print_string @@ show_prog other)
  | Error _ -> print_string "syntax errorRRR"
;;
