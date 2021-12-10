open Lua_lib.Parser
open Lua_lib.Interpreter

let parse_result =
  PStatement.parse_prog
    {|
function fac(n)
  if n <= 1 then
    return 1
  end
  return fac(n - 1) * n
end

c = fac(5)
|}

let () = eval parse_result
