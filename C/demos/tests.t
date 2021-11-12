Cram tests here. They run and compare program output to the expected output
https://dune.readthedocs.io/en/stable/tests.html#cram-tests
Use `dune promote` after you change things that should runned

  $ (./demoParser.exe)
  C_PROG ([C_INCLUDE (["a.h"]);
           TOP_STRUCT_DECL
           ("node",
            [CARGS (CT_INT, "data");
             CARGS (CT_PTR (CT_STRUCT ("node")), "next")]);
           TOP_VAR_DECL ("head", CT_PTR (CT_STRUCT ("node")), None);
           TOP_VAR_DECL
           ("one", CT_PTR (CT_STRUCT ("node")),
            Some (FUNC_CALL
                  (VAR_NAME ("malloc"),
                   [FUNC_CALL
                    (VAR_NAME ("sizeof"), [TYPE (CT_STRUCT ("node"))])])));
           TOP_VAR_DECL
           ("two", CT_PTR (CT_STRUCT ("node")),
            Some (FUNC_CALL
                  (VAR_NAME ("malloc"),
                   [FUNC_CALL
                    (VAR_NAME ("sizeof"), [TYPE (CT_STRUCT ("node"))])])));
           TOP_VAR_DECL
           ("three", CT_PTR (CT_STRUCT ("node")),
            Some (FUNC_CALL
                  (VAR_NAME ("malloc"),
                   [FUNC_CALL
                    (VAR_NAME ("sizeof"), [TYPE (CT_STRUCT ("node"))])])));
           TOP_FUNC_DECL
           (CT_VOID, "insertAtBeginning",
            [CARGS (CT_PTR (CT_PTR (CT_STRUCT ("Node"))), "head_ref");
             CARGS (CT_INT, "new_data")],
            T_BLOCK ([VAR_DECL
                      ("new_node", CT_PTR (CT_STRUCT ("Node")),
                       Some (FUNC_CALL
                             (VAR_NAME ("malloc"),
                              [FUNC_CALL
                               (VAR_NAME ("sizeof"),
                                [TYPE (CT_STRUCT ("Node"))])])));
                      T_ASSIGN
                      (ACCESOR
                       (DEREFERENCE (VAR_NAME ("new_node")), VAR_NAME ("data")),
                       VAR_NAME ("new_data"));
                      T_ASSIGN
                      (ACCESOR
                       (DEREFERENCE (VAR_NAME ("new_node")), VAR_NAME ("next")),
                       DEREFERENCE (VAR_NAME ("head_ref")));
                      T_ASSIGN
                      (DEREFERENCE (VAR_NAME ("head_ref")),
                       VAR_NAME ("new_node"))]));
           TOP_FUNC_DECL
           (CT_VOID, "insertAtEnd",
            [CARGS (CT_PTR (CT_PTR (CT_STRUCT ("Node"))), "head_ref");
             CARGS (CT_INT, "new_data")],
            T_BLOCK ([VAR_DECL
                      ("new_node", CT_PTR (CT_STRUCT ("Node")),
                       Some (FUNC_CALL
                             (VAR_NAME ("malloc"),
                              [FUNC_CALL
                               (VAR_NAME ("sizeof"),
                                [TYPE (CT_STRUCT ("Node"))])])));
                      VAR_DECL
                      ("last", CT_PTR (CT_STRUCT ("Node")),
                       Some (DEREFERENCE (VAR_NAME ("head_ref"))));
                      T_ASSIGN
                      (ACCESOR
                       (DEREFERENCE (VAR_NAME ("new_node")), VAR_NAME ("data")),
                       VAR_NAME ("new_data"));
                      T_ASSIGN
                      (ACCESOR
                       (DEREFERENCE (VAR_NAME ("new_node")), VAR_NAME ("next")),
                       LITERAL (CNULL));
                      IF
                      (EQUAL
                       (DEREFERENCE (VAR_NAME ("head_ref")), LITERAL (CNULL)),
                       T_BLOCK ([T_ASSIGN
                                 (DEREFERENCE (VAR_NAME ("head_ref")),
                                  VAR_NAME ("new_node"));
                                 RETURN (LITERAL (CVOID))]));
                      WHILE
                      (NOT_EQUAL
                       (ACCESOR
                        (DEREFERENCE (VAR_NAME ("last")), VAR_NAME ("next")),
                        LITERAL (CNULL)),
                       T_BLOCK ([T_ASSIGN
                                 (VAR_NAME ("last"),
                                  ACCESOR
                                  (DEREFERENCE (VAR_NAME ("last")),
                                   VAR_NAME ("next")))]));
                      T_ASSIGN
                      (ACCESOR
                       (DEREFERENCE (VAR_NAME ("last")), VAR_NAME ("next")),
                       VAR_NAME ("new_node"));
                      RETURN (LITERAL (CVOID))]));
           TOP_FUNC_DECL
           (CT_VOID, "deleteNode",
            [CARGS (CT_PTR (CT_PTR (CT_STRUCT ("Node"))), "head_ref");
             CARGS (CT_INT, "key")],
            T_BLOCK ([VAR_DECL
                      ("temp", CT_PTR (CT_STRUCT ("Node")),
                       Some (DEREFERENCE (VAR_NAME ("head_ref"))));
                      VAR_DECL
                      ("prev", CT_PTR (CT_STRUCT ("Node")),
                       Some (DEREFERENCE (VAR_NAME ("head_ref"))));
                      IF
                      (AND
                       (NOT_EQUAL (VAR_NAME ("temp"), LITERAL (CNULL)),
                        EQUAL
                        (ACCESOR
                         (DEREFERENCE (VAR_NAME ("temp")), VAR_NAME ("data")),
                         VAR_NAME ("key"))),
                       T_BLOCK ([T_ASSIGN
                                 (DEREFERENCE (VAR_NAME ("head_ref")),
                                  ACCESOR
                                  (DEREFERENCE (VAR_NAME ("temp")),
                                   VAR_NAME ("next")));
                                 EXPRESSION (FUNC_CALL
                                             (VAR_NAME ("free"),
                                              [VAR_NAME ("temp")]));
                                 RETURN (LITERAL (CVOID))]));
                      WHILE
                      (AND
                       (NOT_EQUAL (VAR_NAME ("temp"), LITERAL (CNULL)),
                        NOT_EQUAL
                        (ACCESOR
                         (DEREFERENCE (VAR_NAME ("temp")), VAR_NAME ("data")),
                         VAR_NAME ("key"))),
                       T_BLOCK ([T_ASSIGN
                                 (VAR_NAME ("prev"), VAR_NAME ("temp"));
                                 T_ASSIGN
                                 (VAR_NAME ("temp"),
                                  ACCESOR
                                  (DEREFERENCE (VAR_NAME ("temp")),
                                   VAR_NAME ("next")))]));
                      IF
                      (EQUAL (VAR_NAME ("temp"), LITERAL (CNULL)),
                       T_BLOCK ([RETURN (LITERAL (CVOID))]));
                      T_ASSIGN
                      (ACCESOR
                       (DEREFERENCE (VAR_NAME ("prev")), VAR_NAME ("next")),
                       ACCESOR
                       (DEREFERENCE (VAR_NAME ("temp")), VAR_NAME ("next")));
                      EXPRESSION (FUNC_CALL
                                  (VAR_NAME ("free"), [VAR_NAME ("temp")]))]));
           TOP_FUNC_DECL
           (CT_INT, "searchNode",
            [CARGS (CT_PTR (CT_PTR (CT_STRUCT ("Node"))), "head_ref");
             CARGS (CT_INT, "key")],
            T_BLOCK ([VAR_DECL
                      ("current", CT_PTR (CT_STRUCT ("Node")),
                       Some (DEREFERENCE (VAR_NAME ("head_ref"))));
                      WHILE
                      (NOT_EQUAL (VAR_NAME ("current"), LITERAL (CNULL)),
                       T_BLOCK ([IF
                                 (EQUAL
                                  (ACCESOR
                                   (DEREFERENCE (VAR_NAME ("current")),
                                    VAR_NAME ("data")),
                                   VAR_NAME ("key")),
                                  T_BLOCK ([RETURN (LITERAL (CINT (1)))]));
                                 T_ASSIGN
                                 (VAR_NAME ("current"),
                                  ACCESOR
                                  (DEREFERENCE (VAR_NAME ("current")),
                                   VAR_NAME ("next")))]));
                      RETURN (LITERAL (CINT (0)))]));
           TOP_FUNC_DECL
           (CT_INT, "main", [],
            T_BLOCK ([VAR_DECL
                      ("head", CT_PTR (CT_STRUCT ("Node")),
                       Some (LITERAL (CNULL)));
                      EXPRESSION (FUNC_CALL
                                  (VAR_NAME ("insertAtEnd"),
                                   [ADDRESS (VAR_NAME ("head"));
                                    LITERAL (CINT (1))]));
                      EXPRESSION (FUNC_CALL
                                  (VAR_NAME ("insertAtBeginning"),
                                   [ADDRESS (VAR_NAME ("head"));
                                    LITERAL (CINT (2))]));
                      EXPRESSION (FUNC_CALL
                                  (VAR_NAME ("insertAtBeginning"),
                                   [ADDRESS (VAR_NAME ("head"));
                                    LITERAL (CINT (3))]));
                      EXPRESSION (FUNC_CALL
                                  (VAR_NAME ("insertAtEnd"),
                                   [ADDRESS (VAR_NAME ("head"));
                                    LITERAL (CINT (4))]));
                      EXPRESSION (FUNC_CALL
                                  (VAR_NAME ("insertAfter"),
                                   [ACCESOR
                                    (DEREFERENCE (VAR_NAME ("head")),
                                     VAR_NAME ("next"));
                                    LITERAL (CINT (5))]));
                      EXPRESSION (FUNC_CALL
                                  (VAR_NAME ("deleteNode"),
                                   [ADDRESS (VAR_NAME ("head"));
                                    LITERAL (CINT (3))]));
                      VAR_DECL
                      ("item_to_find", CT_INT, Some (LITERAL (CINT (3))));
                      EXPRESSION (FUNC_CALL
                                  (VAR_NAME ("searchNode"),
                                   [ADDRESS (VAR_NAME ("head"));
                                    VAR_NAME ("item_to_find")]));
                      EXPRESSION (FUNC_CALL
                                  (VAR_NAME ("memcpy"),
                                   [ADDRESS (DEREFERENCE (ADD
                                                          (VAR_NAME ("p"),
                                                           VAR_NAME ("i"))));
                                    ADDRESS (DEREFERENCE (ADD
                                                          (VAR_NAME ("p"),
                                                           VAR_NAME ("j"))));
                                    MUL
                                    (SUB
                                     (VAR_NAME ("n"), VAR_NAME ("constant")),
                                     FUNC_CALL
                                     (VAR_NAME ("sizeof"), [TYPE (CT_INT)]))]));
                      RETURN (LITERAL (CINT (0)))]))])
