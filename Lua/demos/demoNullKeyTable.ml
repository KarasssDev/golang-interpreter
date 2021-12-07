open Lua_lib.Parser
open Lua_lib.Interpreter

let parse_result =
  PStatement.parse_prog {| 
bad_key_table = {[uninitialized_variable] = 3}
|}

let () = eval parse_result
