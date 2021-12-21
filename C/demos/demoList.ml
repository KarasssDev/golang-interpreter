open C_lib.Ast
open C_lib.Parser
open Format
open C_lib.Interpreterctx

let test =
  parse prog
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

    void addHead (struct List *list, int value) {
      struct Node *node = malloc(sizeof(struct Node));
      node->value = value;
      node->next = list->head;
      list->head = node;
    }

    void addTail (struct List *list, int value) {
      struct Node *last = list->head;
      struct Node *node = malloc(sizeof(struct Node));
      
      node->next = NULL;
      node->value = value;

      if (!list->head) {
          list->head = node;
          return;
      }

      while (last->next) {
          last = last->next;
      }
      last->next = node;
    }


    void deleteNodeByVal(struct List* list, int key) {
      struct Node *temp = list->head;
      struct Node *prev = list->head;

      if (temp && (temp->value == key)) {
        list->head = temp->next;
        free(temp);
        return;
      }

      while (temp && temp->value != key) {
        prev = temp;
        temp = temp->next;
      }

      if (!temp) {
        return;
      }

      prev->next = temp->next;

      free(temp);
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

    int main () {
      struct List* l = createList();

      addTail(l, 600);
      addTail(l, 700);
      addTail(l, 800);
      addTail(l, 900);
      addTail(l, 1000);
      addHead(l, 500);
      addHead(l, 400);
      addHead(l, 300);
      addHead(l, 200);
      addHead(l, 100);

      int cntBfr = 0;
      struct Node* it = l->head;
      while(it) {
        if ((cntBfr + 1) % 2 == 0) {
          deleteNodeByVal(l, it->value);
        }
        it = it->next;
        cntBfr++;
      }

      int ans[5];

      int cntAft = 0;
      it = l->head;
      while(it) {
        ans[cntAft] = it->value;
        it = it->next;
        cntAft++;
      }

      int ans0 = ans[0];
      int ans1 = ans[1];
      int ans2 = ans[2];
      int ans3 = ans[3];
      int ans4 = ans[4];

      int cntARm = 0;
      eraseList(l);
      it = l->head;
      while(it) {
        it = it->next;
        cntARm++;
      }
      
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
              [ "cntBfr"; "ans0"; "ans1"; "ans2"; "ans3"; "ans4"; "cntAft"; "cntARm" ]
          with
          | Ok result -> print_string result
          | Error msg -> print_string msg)
      | other -> print_string @@ show_prog other)
  | Error _ -> print_string "syntax errorRRR"
