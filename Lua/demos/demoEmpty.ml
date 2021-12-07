open Lua_lib.Parser
open Lua_lib.Interpreter

let parse_result = PStatement.parse_prog ""
let () = eval parse_result
