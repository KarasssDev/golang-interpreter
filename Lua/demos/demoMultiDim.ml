open Lua_lib.Parser
open Lua_lib.Interpreter

let parse_result =
  PStatement.parse_prog
    {|
  a = {{1, 2, 3},
       {4, 5, 6}}

  b = a[1][2] 
  c = a[2]
  a[2][2] = 20
  |}

let () = eval parse_result
