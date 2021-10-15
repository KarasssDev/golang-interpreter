open Lua_lib.Parser
open Lua_lib.Interpreter

let parse_result =
  PStatement.parse_prog
    {| 
function foo() 
   return "FOO"
end

sample_int_key = 10

table_with_expr_key = {[1] = 5, [17] = 20, [sample_int_key] = 5}

table_with_name_key = {a = 5, foo = 15}

table_mixed = {1, [14] = 5, foo = "poo", 3, [3 * 3] = 9}
|}

let () = eval parse_result
