If-else control stucture tests

  $ ./demoIf.exe
  { vars =
    [["true_inc" ->
       (VFunction (["x"],
          (Block
             [(IfStatement (
                 ((RelOp (Eq, (Var "x"), (Const (VNumber 0.)))),
                  (Block [(Return (Const (VNumber 1.)))])),
                 [((RelOp (Eq, (Var "x"), (Const (VNumber 1.)))),
                   (Block [(Return (Const (VNumber 2.)))]));
                   ((RelOp (Eq, (Var "x"), (Const (VNumber 2.)))),
                    (Block [(Return (Const (VNumber 3.)))]))
                   ],
                 (Some (Block
                          [(Return
                              (ArOp (Sub, (Const (VNumber 0.)),
                                 (Const (VNumber 1.)))))
                            ]))
                 ))
               ])
          ))
    
  "result" -> (VNumber 2.)
  
  ]]
  ; last_value = VNull; is_func = false; is_loop = false; jump_stmt = Default
  }
