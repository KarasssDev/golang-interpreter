open C_lib.Ast
open C_lib.Parser
open Format
open C_lib.Interpreterctx

let test =
  parse prog
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

        int* arr1 = malloc(sizeof(int) * 10);
        for (int i = 0; i < 10; i++) {
          arr1[i] = i * i;
        }

        memcpy(arr1, arr1 + 5 , sizeof(int) * 5);

        int ansNstd0 = arr1[0];
        int ansNstd1 = arr1[1];
        int ansNstd2 = arr1[2];
        int ansNstd3 = arr1[3];
        int ansNstd4 = arr1[4];
        int ansNstd5 = arr1[5];
        int ansNstd6 = arr1[6];
        int ansNstd7 = arr1[7];
        int ansNstd8 = arr1[8];
        int ansNstd9 = arr1[9];

        return (0);
      }

      
    |}

let () =
  match test with
  | Ok prog -> (
      match prog with
      | C_PROG prg -> (
          match
            eval_d prg
              [
                "ans0";
                "ans1";
                "ans2";
                "ans3";
                "ans4";
                "cans0";
                "cans1";
                "cans2";
                "cans3";
                "cans4";
                "ansNstd0";
                "ansNstd1";
                "ansNstd2";
                "ansNstd3";
                "ansNstd4";
                "ansNstd5";
                "ansNstd6";
                "ansNstd7";
                "ansNstd8";
                "ansNstd9";
              ]
          with
          | Ok result -> print_string result
          | Error msg -> print_string msg)
      | other -> print_string @@ show_prog other)
  | Error _ -> print_string "syntax error"
