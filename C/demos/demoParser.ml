open C_lib.Ast
open C_lib.Parser
open Format
open C_lib.Interpreterctx

let test =
  parse prog
    {|
    
      #include <a.h>

      struct node
      {
        int value;
        struct node *next;
      };
      
      struct node0
      {
        int value;
        int value0;
      };

      struct list
      {
        struct node *head;
      };

      int addHead (struct list *list, int value) {
        struct node *node = malloc (1);
        node->value = value;
        node->next = list->head;
        list->head = node;
        return 10;
      }

      int main () {  
        struct list *list = malloc (1);
        
        int a = addHead (list, 100) + addHead (list, 200);

        struct node tst;
        struct node0 tstt = tst;

        return (a * 2);
      }

    |}

let () =
  match test with
  | Ok prog -> 
    (match prog with 
    | C_PROG prg -> 
      (match eval (() |> make_exec_ctx) prg with | Ok result -> print_string @@ result | Error msg -> print_string @@ msg)
      (* print_string  @@ Result.get_ok @@ eval (() |> make_exec_ctx) prg  *)
    | other -> print_string @@ show_prog other)
  (* print_string @@ show_prog prog *)
  | Error _ -> print_string "syntax errorRRR"

(* let () =
  print_string @@ Result.get_ok E.test0 *)