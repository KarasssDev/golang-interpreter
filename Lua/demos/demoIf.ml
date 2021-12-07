open Lua_lib.Parser
open Lua_lib.Interpreter

let parse_result =
  PStatement.parse_prog
    {|
  function true_inc(x)
    if x == 0 then
      return 1
    elseif x == 1 then 
      return 2
    elseif x == 2 then
      return 3
    else
      return -1
    end
  end
  
  result = true_inc(1)
  |}

let () = eval parse_result
