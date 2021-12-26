open Tester

let%test _ = Tester.test_typing {|
  1 + ( 2 + 5)
|} TInt
