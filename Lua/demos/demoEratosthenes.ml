open Lua_lib.Parser
open Lua_lib.Interpreter

let parse_result =
  PStatement.parse_prog
    {|
function get_sieve_from_zero(upper_bound)
    local sieve = {}
    for i = 0, upper_bound do 
        sieve[i] = true 
    end
    
    sieve[0], sieve[1] = false, false
    
    for i = 0, upper_bound do
        if sieve[i] then 
            for j = i * i, upper_bound, i do
                sieve[j] = false 
            end
        end
    end
    
    return sieve
end


sieve = get_sieve_from_zero(100)
prime_count = 0

for i = 0, 100 do 
    if sieve[i] then
        prime_count = prime_count + 1
    end
end
|}

let () = eval parse_result
