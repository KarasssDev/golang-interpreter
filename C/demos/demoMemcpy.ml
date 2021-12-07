open C_lib.Ast
open C_lib.Parser
open Format
open C_lib.Interpreterctx

let test =
  parse
    prog
    {|
      
      #include <a.h>

      void* memcpy (void *dst, void *src, int len) {
        char * cdst = dst;
        char * csrc = src;

        int i = 0;
        while (i < len) {
          *(cdst + i) = *(csrc + i);
          i++;
        }

        return dst;
      }

      int main () {
        int* arr = malloc(sizeof(int) * 5);

        for (int i = 1; i <= 5; i++) {
          arr[i - 1] = i * 100;
        }

        int* carr = malloc(sizeof(int) * 5);
        
        memcpy(carr, arr, sizeof(int) * 5);
        
        int ans0 = arr[0];
        int ans1 = arr[1];
        int ans2 = arr[2];
        int ans3 = arr[3];
        int ans4 = arr[4];

        int cans0 = carr[0];
        int cans1 = carr[1];
        int cans2 = carr[2];
        int cans3 = carr[3];
        int cans4 = carr[4];

        return (0);
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
           ; "cans0"
           ; "cans1"
           ; "cans2"
           ; "cans3"
           ; "cans4"
           ]
       with
      | Ok result -> print_string @@ result
      | Error msg -> print_string @@ msg)
    | other -> print_string @@ show_prog other)
  | Error _ -> print_string "syntax errorRRR"
;;
