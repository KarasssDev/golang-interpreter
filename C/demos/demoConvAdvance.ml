open C_lib.Ast
open C_lib.Parser
open Format
open C_lib.Interpreterctx

let test =
  parse prog
    {|
      
      struct A {
        int a;
        int b;
      };

      int main () {
        int *pt = malloc(sizeof(int));
        struct A* a = pt;
        
        *pt = 100;
        int ans0 = *pt;
        
        struct A b = {300, 500};
        *a = b;
        int ans1 = *a;
        
        *pt += 700;
        int ans2 = *a;
        
        return 0; 
      }

    |}

let () =
  match test with
  | Ok prog -> (
      match prog with
      | C_PROG prg -> (
          match eval_d prg [ "ans0"; "ans1"; "ans2" ] with
          | Ok result -> print_string result
          | Error msg -> print_string msg)
      | other -> print_string @@ show_prog other)
  | Error _ -> print_string "syntax error"
