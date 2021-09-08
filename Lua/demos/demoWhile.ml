open Lua_lib.Parser
open Lua_lib.Interpreter

let parse_result =
  PStatement.parse_prog
    {|
function is_prime(x)
  if x == 1 then return false end
  local i = 2
  while i * i <= x do
      if x % i == 0 then
        return false
      end
      i = i + 1
  end 
  return true
end

result = is_prime(100)
  |}

let () = eval parse_result
