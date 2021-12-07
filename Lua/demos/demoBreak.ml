open Lua_lib.Parser
open Lua_lib.Interpreter

let parse_result =
  PStatement.parse_prog
    {|
s = 0
for i = 1, 5 do 
  if i % 2 == 0 then
    break
  end
  s = s + 1
end
|}

let () = eval parse_result
