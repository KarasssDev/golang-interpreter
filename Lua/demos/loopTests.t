'Numerical for' and 'while' statements tests

  $ ./demoForNumerical.exe
  { vars = [["s" -> (VNumber 100.)
    
  ]]
  ; last_value = VNull; prev_env = None; is_func = false; is_loop = true;
  jump_stmt = Default; last_env = None
  }
  $ ./demoWhile.exe
  { vars =
    [["is_prime" ->
       (VFunction (["x"],
          (Block
             [(If
                 [((RelOp (Eq, (Var "x"), (Const (VNumber 1.)))),
                   (Block [(Return (Const (VBool false)))]))]);
               (Local (VarDec [((Var "i"), (Const (VNumber 2.)))]));
               (While (
                  (RelOp (Leq, (ArOp (Mul, (Var "i"), (Var "i"))), (Var "x"))),
                  (Block
                     [(If
                         [((RelOp (Eq, (ArOp (Mod, (Var "x"), (Var "i"))),
                              (Const (VNumber 0.)))),
                           (Block [(Return (Const (VBool false)))]))]);
                       (VarDec
                          [((Var "i"),
                            (ArOp (Sum, (Var "i"), (Const (VNumber 1.)))))])
                       ])
                  ));
               (Return (Const (VBool true)))])
          ))
    
  "result" -> (VBool false)
  
  ]]
  ; last_value = VNull; prev_env = None; is_func = false; is_loop = false;
  jump_stmt = Default; last_env = None
  }

  $ ./demoBreak.exe
  { vars = [["s" -> (VNumber 1.)
    
  ]]
  ; last_value = VNull; prev_env = None; is_func = false; is_loop = true;
  jump_stmt = Default; last_env = None
  }
