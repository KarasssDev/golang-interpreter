open Tester

let%test _ = Tester.test_parse {|

let x = f5

|} []

