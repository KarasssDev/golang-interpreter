open Tester

let%test _ = Tester.test_typing {|
  let rec fix f x = f (fix f) x in fix
|} TInt
