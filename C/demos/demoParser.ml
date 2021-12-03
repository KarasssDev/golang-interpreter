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

      struct Node {
          int value;
          struct Node *next;
      };

      struct List {
          struct Node *head;
      };

      struct List* createList () {
        struct List *list = malloc(sizeof(struct List));
        list->head = NULL;
        return list;
      }

      struct Node* createNode (int value) {
          struct Node *node = malloc(sizeof(struct Node));
          node->value = value;
          node->next = NULL;
          return node;
      }

      void addHead (struct List *list, int value) {
          struct Node *node = malloc(sizeof(struct Node));
          node->value = value;
          node->next = list->head;
          list->head = node;
      }

      void addTail (struct List *list, int value) {
          struct Node *node;
          if (list->head) {
              node = list->head;
              while (node->next) {
                  node = node->next;
              }
              node->next = createNode(value);
          } else {
              list->head = createNode(value);
          }
      }

      void deleteFstEntry (struct List *list, int value) {
          if (list->head->next) {
              struct Node *before;
              before = list->head;
              struct Node *after;
              after = list->head->next;
      
              while (after) {
                  if (after->value == value) {
                      struct Node *toDelete;
                      toDelete = after;
                      if (toDelete->next) {
                          after = toDelete->next;
                          before->next = after;
                          free(toDelete);
                      } else {
                          after = NULL;
                          before->next = after;
                          free(toDelete);
                      }
                  } else {
                      after = after->next;
                      before= before->next;
                  }
              }
          } 

          if (list->head->value == value) {
              struct Node *toDelete;
              toDelete = list->head;
              list->head = toDelete->next;
              free(toDelete);
          }
      }

      void eraseList (struct List *list) {
          struct Node *node = list->head;
          struct Node *toDeletee;
          while (node) {
              toDeletee = node;
              node = node->next;
              free(toDeletee);
          }
          list->head = NULL;
          free(list);
      }

      int factorial (int n) {  
        if (n == 0) {  
          return 1;
        }  
        else{
          return(n * factorial(n - 1));
        }
      }  

      int main () {

        struct List* l = createList();
        
        addTail(l, 100);
        addTail(l, 200);
        addTail(l, 300);
        addTail(l, 400);
        addTail(l, 500);
        addHead(l, -100);
        
        struct Node* it = l->head;
        int cnt = 0;
        while (it) {
          it = it->next;
          cnt++;
        }

        eraseList(l);

        int a = factorial (5);

        return (factorial (5));
      }
      
    |}


    (* 
      void* memcpy (void *dst, void *src, int len) {
        char * char_dst = dst;
        char * char_src = src;

        int i = 0;
        while (i < 5) {
          *(char_dst + i) = *(char_src + i);
          i = i + 1;
        }
        return 1;
      }
    *)
(* 
 struct list *list = malloc (1);
        
        int a = addHead (list, 100) + addHead (list, 200);

        struct node tst;
        struct node0 tstt = tst;

        return (a * 2);

*)

(* 
      void* memcpy (void *dst, void *src, int len) {
        char *char_dst = dst;
        char *char_src = src;

        int i = 0;
        while (i < 5) {
          *(char_dst + i) = *(char_src + i);
          i = i + 1;
        }
      }
*)

let () =
  match test with
  | Ok prog -> 
    (match prog with 
    | C_PROG prg -> 
      (match eval prg with 
        | Ok result -> print_string @@ result 
        | Error msg -> print_string @@ msg)
    | other -> print_string @@ show_prog other)
  (* print_string @@ show_prog prog *)
  | Error _ -> print_string "syntax errorRRR"
  (* print_string  @@ Result.get_ok @@ E.test1 *)

(* let () =
  print_string @@ Result.get_ok E.test0 *)