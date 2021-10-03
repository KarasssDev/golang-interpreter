open C_lib.Ast
open C_lib.Parser
open Format

let test =
  parse prog
    {|
    
      #include <a.h>

      struct node
      {
        int data;
        struct node *next;
      };
      
      struct node *head;
      
      struct node *one = malloc(sizeof(struct node));
      
      struct node *two = malloc(sizeof(struct node));
      
      struct node *three = malloc(sizeof(struct node));
      
      void insertAtBeginning(struct Node** head_ref, int new_data) {
        struct Node* new_node = malloc(sizeof(struct Node));
        new_node->data = new_data;
        new_node->next = *head_ref;
        *head_ref = new_node;
      }

      void insertAtEnd(struct Node** head_ref, int new_data) {
        struct Node* new_node = malloc(sizeof(struct Node));
        struct Node* last = *head_ref;

        new_node->data = new_data;
        new_node->next = NULL;

        if (*head_ref == NULL) {
          *head_ref = new_node;
          return;
        }

        while (last->next != NULL) {
          last = last->next;
        }

        last->next = new_node;
        return;
      }

      void deleteNode(struct Node** head_ref, int key) {
        struct Node *temp = *head_ref; 
        struct Node *prev = *head_ref;

        if (temp != NULL && temp->data == key) {
          *head_ref = temp->next;
          free(temp);
          return;
        }
        while (temp != NULL && temp->data != key) {
          prev = temp;
          temp = temp->next;
        }

        if (temp == NULL) {
          return;
        }

        prev->next = temp->next;

        free(temp);
      }

      int searchNode(struct Node** head_ref, int key) {
        struct Node* current = *head_ref;

        while (current != NULL) {
          if (current->data == key) {
            return 1;
          }
          current = current->next;
        }

        return 0;
      }

      int main () {  
        struct Node* head = NULL;

        insertAtEnd(&head, 1);
        insertAtBeginning(&head, 2);
        insertAtBeginning(&head, 3);
        insertAtEnd(&head, 4);

        insertAfter(head->next, 5);

        deleteNode(&head, 3);
        int item_to_find = 3;
        searchNode(&head, item_to_find);

        memcpy(&(*(p+i)), &(*(p+j)), (n - constant) * sizeof(int));
        
        int a[];
        return 0;
      }

      |}

let () =
  match test with
  | Ok prog -> print_string @@ show_prog prog
  | Error _ -> print_string "syntax error"
