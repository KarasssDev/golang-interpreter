open Tester
open Ast

let%test _ = Tester.test_typing {| [] :: 1 |} TInt

type 'a list =
  | Nil
  | Cons of 'a * 'a list
