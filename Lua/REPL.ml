open Lua_lib.Interpreter
open Lua_lib.Parser
open Eval (Result)

let stdlib =
  {|
  function abs(x)
    if x >= 0 then
      return x
    else
      return -x
    end
  end

  function gcd(a, b)
    while a > 0 and b > 0 do 
       if a > b then
         a = a % b
       else 
         b = b % a 
       end
    end
    return a + b 
  end
  
  function fib(n)
    if n <= 1 then return n end
    local fib0, fib1, fib = 0, 1, 0
    for i = 1, n - 1 do
      fib = fib0 + fib1
      fib0, fib1 = fib1, fib
    end
    return fib
  end

  function pow(x, n)
    if n == 0 then 
      return 1
    end
    if n % 2 == 1 then 
      return x * pow(x, n - 1)
    end
    local fp = pow(x, n // 2)
    return fp * fp
  end
  |}

let rec print_lst = function
  | [] -> print_endline "[]\n=======\n"
  | hd :: tl ->
      print_endline @@ show_environment hd;
      print_lst tl

let rec repl env_lst buffer =
  let str = print_string ">>> "; read_line () in
  let check_end_of_input s =
    let is_end_of_input = function
      | "" -> false
      | s -> s.[String.length s - 1] == '@' in
    let del_end_of_input s = String.sub s 0 (String.length s - 1) in
    if is_end_of_input s then (
      Buffer.add_string buffer (del_end_of_input s);
      match PStatement.parse_prog (Buffer.contents buffer) with
      | Some parsed_prog -> (
        match parsed_prog with
        | Block b -> (
          match eval_block env_lst b with
          | Ok res ->
              let last_value = (List.hd res).last_value in
              if string_of_value last_value <> "nil" then
                print_endline @@ string_of_value last_value;
              Buffer.clear buffer;
              repl res buffer
          | Error msg ->
              print_endline msg; Buffer.clear buffer; repl env_lst buffer )
        | _ -> () )
      | None ->
          print_endline "Error: Syntax error occured";
          Buffer.clear buffer;
          repl env_lst buffer )
    else Buffer.add_string buffer (str ^ "\n");
    repl env_lst buffer in
  check_end_of_input str

let () =
  print_endline "===== Lua REPL =====";
  print_endline "Each command should end with '@' character";
  let buffer = Buffer.create 1024 in
  match PStatement.parse_prog stdlib with
  | Some parsed_library -> (
    match eval_stmt [] parsed_library with
    | Ok env -> repl env buffer
    | Error _ -> print_endline "Error: Couldn't evaluate standart library" )
  | None -> print_endline "Error: Couldn't load standart library"
