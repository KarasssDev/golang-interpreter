open C_lib.Ast
open C_lib.Parser
open Format
open C_lib.Interpreterctx

let test =
  parse
    prog
    {|
      
      #include <a.h>
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


      struct List* l;
      
      int a0;
      int a1;
      int a2;
      int a3;
      int a4;
      int a5;
      int a6;

      void actions () {
        int ans[6];
        
        l = createList();
        
        addTail(l, 100);
        addTail(l, 200);
        addTail(l, 200);
        addTail(l, 400);
        addTail(l, 500);
        addHead(l, -100);

        struct Node* it = l->head;
        int cnt = 0;
        while (it) {
          ans[cnt] = it->value;
          it = it->next;
          cnt++;
        }
        
        a0 = ans[0];
        a1 = ans[1];
        a2 = ans[2];
        a3 = ans[3];
        a4 = ans[4];
        a5 = ans[5];
        a6 = cnt;

        eraseList(l);

      }


      int main () {

        actions();

        int ans0 = a0;
        int ans1 = a1;
        int ans2 = a2;
        int ans3 = a3;
        int ans4 = a4;
        int ans5 = a5;
        int cntBfr = a6;


        struct Node* it = l->head;
        int cnt = 0;
        while (it) {
          it = it->next;
          cnt++;
        }

        int cntAft = cnt;
        

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
         eval_d prg [ "cntBfr"; "ans0"; "ans1"; "ans2"; "ans3"; "ans4"; "ans5"; "cntAft" ]
       with
      | Ok result -> print_string @@ result
      | Error msg -> print_string @@ msg)
    | other -> print_string @@ show_prog other)
  | Error _ -> print_string "syntax errorRRR"
;;
