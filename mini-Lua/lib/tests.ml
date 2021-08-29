open Ast
open Parser
open Parser.PExpression
open Parser.PStatement

(* Expression tests *)

let%test _ = apply float_parser "1." = Some 1.

let%test _ = apply int_parser "  1" = Some 1

let%test _ = apply float_parser ".15" = None

let%test _ = apply ident "_Test_1_" = Some "_Test_1_"

let%test _ = apply ident "if" = None

let%test _ = apply ident "123Test" = None

let%test _ = apply const_number "1.15" = Some (Const (VFloat 1.15))

let%test _ = apply const_number " .15" = None

let%test _ = apply const_number "  3" = Some (Const (VInt 3))

let%test _ = apply const_bool "true  " = Some (Const (VBool true))

let%test _ = apply const_null "nil" = Some (Const VNull)

let%test _ =
  apply const_string "\" sample \"" = Some (Const (VString " sample "))

let%test _ = apply const_string "\"\"" = Some (Const (VString ""))

let%test _ =
  apply create_table "{a = 5}"
  = Some (TableCreate [ Assign (Var "a", Const (VInt 5)) ])

let%test _ =
  apply table_access "data[3]" = Some (TableAccess (Var "data", Const (VInt 3)))

let%test _ = apply expr "-5" = Some (ArOp (Sub, Const (VInt 0), Const (VInt 5)))

let%test _ = apply expr "a = 5" = Some (Assign (Var "a", Const (VInt 5)))

let%test _ =
  apply expr "a = {b = 5}"
  = Some (Assign (Var "a", TableCreate [ Assign (Var "b", Const (VInt 5)) ]))

let%test _ =
  apply call_func "foo   (a=3, 5)"
  = Some
      (CallFunc (Var "foo", [ Assign (Var "a", Const (VInt 3)); Const (VInt 5) ]))

(* Statement tests *)

let%test _ = apply return_stmt "return a" = Some (Return (Var "a"))

let%test _ = apply return_stmt "return" = Some (Return (Const VNull))

let%test _ = apply break_stmt "break" = Some Break

let%test _ =
  apply var_dec_stmt "a, b = 1, 2"
  = Some (VarDec [ (Var "a", Const (VInt 1)); (Var "b", Const (VInt 2)) ])

let%test _ =
  apply var_dec_stmt "a, b = 1"
  = Some (VarDec [ (Var "a", Const (VInt 1)); (Var "b", Const VNull) ])

let%test _ =
  apply var_dec_stmt "a = 1, 2" = Some (VarDec [ (Var "a", Const (VInt 1)) ])

let%test _ =
  apply block_stmt "do a = 1, 2 end"
  = Some (Block [ VarDec [ (Var "a", Const (VInt 1)) ] ])

let%test _ =
  apply expr_stmt "a = 3" = Some (Expression (Assign (Var "a", Const (VInt 3))))

let%test _ =
  apply while_stmt "while a == true do a = false end"
  = Some
      (While
         ( RelOp (Eq, Var "a", Const (VBool true)),
           Block [ VarDec [ (Var "a", Const (VBool false)) ] ] ))

let%test _ =
  apply for_num_stmt "for i = 1,5,2 do 1 2 end"
  = Some
      (ForNumerical
         ( Var "i",
           [ Const (VInt 1); Const (VInt 5); Const (VInt 2) ],
           Block [ Expression (Const (VInt 1)); Expression (Const (VInt 2)) ] ))

let%test _ = apply for_num_stmt "for i = 1 do 1 end" = None

let%test _ =
  apply if_stmt "if true then false elseif false then true false else false end"
  = Some
      (If
         [
           (Const (VBool true), Block [ Expression (Const (VBool false)) ]);
           ( Const (VBool false),
             Block
               [
                 Expression (Const (VBool true));
                 Expression (Const (VBool false));
               ] );
           (Const (VBool true), Block [ Expression (Const (VBool false)) ]);
         ])

let%test _ = apply if_stmt "if true then false" = None

let%test _ =
  apply if_stmt "if true then false elseif false then false end"
  = Some
      (If
         [
           (Const (VBool true), Block [ Expression (Const (VBool false)) ]);
           (Const (VBool false), Block [ Expression (Const (VBool false)) ]);
         ])

let%test _ =
  apply if_stmt "if true then false else false elseif true then false end"
  = None

let%test _ =
  apply func_stmt "function a(x, y) return x + y end"
  = Some
      (FuncDec
         ("a", [ "x"; "y" ], Block [ Return (ArOp (Sum, Var "x", Var "y")) ]))

(* Parse all *)

(* factorial.lua *)
let%test _ =
  apply parse_all
    "\n\
     function fact (n)\n\
    \    if n == 0 then\n\
    \        return 1\n\
    \    else \n\
    \        return n * fact (n - 1)\n\
    \    end\n\
     end\n\n\n\
     data = {1, 2, 3, 4, 5, 6, 7}\n\
     s = 0\n\
     s = s + fact (data[i])\n\
     for i = 1,7 do\n\
    \    s = s + fact(data[i])\n\
     end\n"
  = Some
      (Block
         [
           FuncDec
             ( "fact",
               [ "n" ],
               Block
                 [
                   If
                     [
                       ( RelOp (Eq, Var "n", Const (VInt 0)),
                         Block [ Return (Const (VInt 1)) ] );
                       ( Const (VBool true),
                         Block
                           [
                             Return
                               (ArOp
                                  ( Mul,
                                    Var "n",
                                    CallFunc
                                      ( Var "fact",
                                        [ ArOp (Sub, Var "n", Const (VInt 1)) ]
                                      ) ));
                           ] );
                     ];
                 ] );
           VarDec
             [
               ( Var "data",
                 TableCreate
                   [
                     Const (VInt 1);
                     Const (VInt 2);
                     Const (VInt 3);
                     Const (VInt 4);
                     Const (VInt 5);
                     Const (VInt 6);
                     Const (VInt 7);
                   ] );
             ];
           VarDec [ (Var "s", Const (VInt 0)) ];
           VarDec
             [
               ( Var "s",
                 ArOp
                   ( Sum,
                     Var "s",
                     CallFunc (Var "fact", [ TableAccess (Var "data", Var "i") ])
                   ) );
             ];
           ForNumerical
             ( Var "i",
               [ Const (VInt 1); Const (VInt 7) ],
               Block
                 [
                   VarDec
                     [
                       ( Var "s",
                         ArOp
                           ( Sum,
                             Var "s",
                             CallFunc
                               ( Var "fact",
                                 [ TableAccess (Var "data", Var "i") ] ) ) );
                     ];
                 ] );
         ])

(* use_local.lua *)
let () =
  print_newline ();
  print_newline ()

let%test _ =
  apply parse_all
    {|  
x = 10

function xChanger(value)
    local x = value
    print(x)
end 

xChanger(5)

print(x)
|}
  = Some
      (Block
         [
           VarDec [ (Var "x", Const (VInt 10)) ];
           FuncDec
             ( "xChanger",
               [ "value" ],
               Block
                 [
                   Local (VarDec [ (Var "x", Var "value") ]);
                   Expression (CallFunc (Var "print", [ Var "x" ]));
                 ] );
           Expression (CallFunc (Var "xChanger", [ Const (VInt 5) ]));
           Expression (CallFunc (Var "print", [ Var "x" ]));
         ])

let () = print_newline ()
