open C_lib.Ast
open C_lib.Parser
open Format
open C_lib.Interpreterctx

let test =
  parse prog
    {|
      #include <a.h>

      struct A {
        char aa;
        char ba;
      };

      struct B {
        char ab;
        char bb;
      };

      int main () {
        struct A a = {'a', 'A'};
        
        
        struct B b = a;
        
        a.aa = 'Y';
        a.ba = 'Y';

        char ansAaa = a.aa;
        char ansBba = a.ba;

        char ansBab = b.ab;
        char ansBbb = b.bb;

        return (0);
      }
    |}

let () =
  match test with
  | Ok prog -> (
      match prog with
      | C_PROG prg -> (
          match eval_d prg [ "ansAaa"; "ansBba"; "ansBab"; "ansBbb" ] with
          | Ok result -> print_string @@ result
          | Error msg -> print_string @@ msg)
      | other -> print_string @@ show_prog other)
  | Error _ -> print_string "syntax errorRRR"
