open Lua_lib.Parser
open Lua_lib.Interpreter

let parse_result =
  PStatement.parse_prog
    {|
s = 0
for i = 1, 10 do
  for j = 1, 10 do 
    s = s + 1
  end
end
|}

let () = eval parse_result
