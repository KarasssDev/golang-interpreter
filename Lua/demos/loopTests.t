'Numerical for' and 'while' statements tests

  $ ./demoForNumerical.exe
  { vars = [["s" -> (VNumber 100.)
    
  ]]
  ; last_value = VNull; is_func = false; is_loop = false; jump_stmt = Default
  }
  $ ./demoWhile.exe
  { vars =
    [["is_prime" ->
       (VFunction (["x"],
          (Block
             [(IfStatement (
                 ((RelOp (Eq, (Var "x"), (Const (VNumber 1.)))),
                  (Block [(Return (Const (VBool false)))])),
                 [], None));
               (Local (VarDec [((Var "i"), (Const (VNumber 2.)))]));
               (While (
                  (RelOp (Leq, (ArOp (Mul, (Var "i"), (Var "i"))), (Var "x"))),
                  (Block
                     [(IfStatement (
                         ((RelOp (Eq, (ArOp (Mod, (Var "x"), (Var "i"))),
                             (Const (VNumber 0.)))),
                          (Block [(Return (Const (VBool false)))])),
                         [], None));
                       (VarDec
                          [((Var "i"),
                            (ArOp (Sum, (Var "i"), (Const (VNumber 1.)))))])
                       ])
                  ));
               (Return (Const (VBool true)))])
          ))
    
  "result" -> (VBool false)
  
  ]]
  ; last_value = VNull; is_func = false; is_loop = false; jump_stmt = Default
  }

  $ ./demoBreak.exe
  { vars = [["s" -> (VNumber 1.)
    
  ]]
  ; last_value = VNull; is_func = false; is_loop = false; jump_stmt = Default
  }
