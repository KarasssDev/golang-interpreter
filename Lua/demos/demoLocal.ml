open Lua_lib.Parser
open Lua_lib.Interpreter

let parse_result =
  PStatement.parse_prog
    {|
 x = 5 
 if true then
  local x = 10
  x = 15
 end
  |}

let () = eval parse_result
