open Ast
open Parser
open Parser.PExpression
open Parser.PStatement

(* ==== Expression tests ==== *)

let%test _ = apply ident "_Test_1_" = Some "_Test_1_"
let%test _ = apply ident "if" = None
let%test _ = apply ident "123Test" = None
let%test _ = apply const_number "1.15" = Some (Const (VNumber 1.15))
let%test _ = apply const_number " .15" = None
let%test _ = apply const_number "  3" = Some (Const (VNumber 3.))
let%test _ = apply const_bool "true  " = Some (Const (VBool true))
let%test _ = apply const_null "nil" = Some (Const VNull)

let%test _ =
  apply const_string "\" sample \"" = Some (Const (VString " sample "))

let%test _ = apply const_string "\"\"" = Some (Const (VString ""))

let%test _ =
  apply create_table "{a = 5}"
  = Some (TableCreate [Assign (Var "a", Const (VNumber 5.))])

let%test _ =
  apply table_access "data[3]" = Some (TableAccess ("data", Const (VNumber 3.)))

let%test _ =
  apply expr "-5" = Some (ArOp (Sub, Const (VNumber 0.), Const (VNumber 5.)))

let%test _ = apply expr "a = 5" = Some (Assign (Var "a", Const (VNumber 5.)))

let%test _ =
  apply expr "a = {b = 5}"
  = Some (Assign (Var "a", TableCreate [Assign (Var "b", Const (VNumber 5.))]))

let%test _ =
  apply call_func "foo   (a=3, 5)"
  = Some
      (CallFunc
         ("foo", [Assign (Var "a", Const (VNumber 3.)); Const (VNumber 5.)]) )

(* ==== Statement tests ==== *)

let%test _ = apply return_stmt "return a" = Some (Return (Var "a"))
let%test _ = apply return_stmt "return" = Some (Return (Const VNull))
let%test _ = apply break_stmt "break" = Some Break

let%test _ =
  apply var_dec_stmt "a, b = 1, 2"
  = Some (VarDec [(Var "a", Const (VNumber 1.)); (Var "b", Const (VNumber 2.))])

let%test _ =
  apply var_dec_stmt "a, b = 1"
  = Some (VarDec [(Var "a", Const (VNumber 1.)); (Var "b", Const VNull)])

let%test _ =
  apply var_dec_stmt "a = 1, 2" = Some (VarDec [(Var "a", Const (VNumber 1.))])

let%test _ =
  apply block_stmt "do a = 1, 2 end"
  = Some (Block [VarDec [(Var "a", Const (VNumber 1.))]])

let%test _ =
  apply expr_stmt "a = 3"
  = Some (Expression (Assign (Var "a", Const (VNumber 3.))))

let%test _ =
  apply while_stmt "while a == true do a = false end"
  = Some
      (While
         ( RelOp (Eq, Var "a", Const (VBool true))
         , Block [VarDec [(Var "a", Const (VBool false))]] ) )

let%test _ =
  apply for_num_stmt "for i = 1,5,2 do 1 2 end"
  = Some
      (ForNumerical
         ( "i"
         , [Const (VNumber 1.); Const (VNumber 5.); Const (VNumber 2.)]
         , Block
             [Expression (Const (VNumber 1.)); Expression (Const (VNumber 2.))]
         ) )

let%test _ = apply for_num_stmt "for i = 1 do 1 end" = None

let%test _ =
  apply if_stmt "if true then false elseif false then true false else false end"
  = Some
      (If
         [ (Const (VBool true), Block [Expression (Const (VBool false))])
         ; ( Const (VBool false)
           , Block
               [ Expression (Const (VBool true))
               ; Expression (Const (VBool false)) ] )
         ; (Const (VBool true), Block [Expression (Const (VBool false))]) ] )

let%test _ = apply if_stmt "if true then false" = None

let%test _ =
  apply if_stmt "if true then false elseif false then false end"
  = Some
      (If
         [ (Const (VBool true), Block [Expression (Const (VBool false))])
         ; (Const (VBool false), Block [Expression (Const (VBool false))]) ] )

let%test _ =
  apply if_stmt "if true then false else false elseif true then false end"
  = None

let%test _ =
  apply func_stmt "function a(x, y) return x + y end"
  = Some
      (FuncDec ("a", ["x"; "y"], Block [Return (ArOp (Sum, Var "x", Var "y"))]))

(* === Parse Lua Program tests === *)

let%test _ =
  parse_prog
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
         [ FuncDec
             ( "fact"
             , ["n"]
             , Block
                 [ If
                     [ ( RelOp (Eq, Var "n", Const (VNumber 0.))
                       , Block [Return (Const (VNumber 1.))] )
                     ; ( Const (VBool true)
                       , Block
                           [ Return
                               (ArOp
                                  ( Mul
                                  , Var "n"
                                  , CallFunc
                                      ( "fact"
                                      , [ArOp (Sub, Var "n", Const (VNumber 1.))]
                                      ) ) ) ] ) ] ] )
         ; VarDec
             [ ( Var "data"
               , TableCreate
                   [ Const (VNumber 1.); Const (VNumber 2.); Const (VNumber 3.)
                   ; Const (VNumber 4.); Const (VNumber 5.); Const (VNumber 6.)
                   ; Const (VNumber 7.) ] ) ]
         ; VarDec [(Var "s", Const (VNumber 0.))]
         ; VarDec
             [ ( Var "s"
               , ArOp
                   ( Sum
                   , Var "s"
                   , CallFunc ("fact", [TableAccess ("data", Var "i")]) ) ) ]
         ; ForNumerical
             ( "i"
             , [Const (VNumber 1.); Const (VNumber 7.)]
             , Block
                 [ VarDec
                     [ ( Var "s"
                       , ArOp
                           ( Sum
                           , Var "s"
                           , CallFunc ("fact", [TableAccess ("data", Var "i")])
                           ) ) ] ] ) ] )

let%test _ =
  parse_prog
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
         [ VarDec [(Var "x", Const (VNumber 10.))]
         ; FuncDec
             ( "xChanger"
             , ["value"]
             , Block
                 [ Local (VarDec [(Var "x", Var "value")])
                 ; Expression (CallFunc ("print", [Var "x"])) ] )
         ; Expression (CallFunc ("xChanger", [Const (VNumber 5.)]))
         ; Expression (CallFunc ("print", [Var "x"])) ] )

let%test _ =
  parse_prog
    {|
function binop(x, y, op)
  local result = op(x, y)
  return result
end

function prod(x, y)
  return x * y
end


a = 5
b = 4
print(binop(a, b, prod))    
|}
  = Some
      (Block
         [ FuncDec
             ( "binop"
             , ["x"; "y"; "op"]
             , Block
                 [ Local
                     (VarDec
                        [(Var "result", CallFunc ("op", [Var "x"; Var "y"]))] )
                 ; Return (Var "result") ] )
         ; FuncDec
             ("prod", ["x"; "y"], Block [Return (ArOp (Mul, Var "x", Var "y"))])
         ; VarDec [(Var "a", Const (VNumber 5.))]
         ; VarDec [(Var "b", Const (VNumber 4.))]
         ; Expression
             (CallFunc
                ("print", [CallFunc ("binop", [Var "a"; Var "b"; Var "prod"])])
             ) ] )
