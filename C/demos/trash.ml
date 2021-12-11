(* open C_lib.Ast
   open C_lib.Parser
   open Format
   open C_lib.Interpreterctx

   let test =
     parse prog
       {|
            #include <a.h>

            struct St {
              int a;
            };

            struct Stt {
             struct St ss[5];
            };

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

              struct Stt s;

              return (0);
            }

          |}

   (*
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
                    struct Node *before = list->head;
                    struct Node *after = list->head->next;

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
              else {
                return(n * factorial(n - 1));
              }
            }


            int a = 10;



            int main () {

              struct List* l = createList();

              addTail(l, 100);
              addTail(l, 200);
              addTail(l, 200);
              addTail(l, 400);
              addTail(l, 500);
              addHead(l, -100);

              deleteFstEntry(l, 100);
              deleteFstEntry(l, 200);
              deleteFstEntry(l, 200);


              struct Node* it = l->head;
              int cnt = 0;
              while (it) {
                it = it->next;
                cnt++;
              }



              return (factorial (5));
            }
          *)

   let () =
     match test with
     | Ok prog -> (
         match prog with
         | C_PROG prg -> (
             match
               eval_dd prg [ "ans00"; "ans01"; "ans02"; "ans10"; "ans11"; "ans12" ]
             with
             | Ok result -> print_string @@ result
             | Error msg -> print_string @@ msg)
         | other -> print_string @@ show_prog other)
     (* print_string @@ show_prog prog *)
     | Error _ -> print_string "syntax errorRRR"
   (* print_string  @@ Result.get_ok @@ E.test1 *)

   (* let () =
      print_string @@ Result.get_ok E.test0 *) *)
