Complex tests of lua interpreter available features

  $ ./demoHighFunctions.exe
  { vars =
    [["add" ->
       (VFunction (["x"; "y"],
          (Block [(Return (ArOp (Sum, (Var "x"), (Var "y"))))])))
    
  "binop" ->
   (VFunction (["x"; "y"; "op"],
      (Block [(Return (CallFunc ("op", [(Var "x"); (Var "y")])))])))
  
  "c" -> (VNumber 12.)
  
  "sub" ->
   (VFunction (["x"; "y"],
      (Block [(Return (ArOp (Sub, (Var "x"), (Var "y"))))])))
  
  ]]
  ; last_value = VNull; is_func = false; is_loop = false; jump_stmt = Default
  }

  $ ./demoEratosthenes.exe
  { vars =
    [["get_sieve_from_zero" ->
       (VFunction (["upper_bound"],
          (Block
             [(Local (VarDec [((Var "sieve"), (TableCreate []))]));
               (ForNumerical ("i", [(Const (VNumber 0.)); (Var "upper_bound")],
                  (Block
                     [(VarDec
                         [((TableAccess ("sieve", (Var "i"))),
                           (Const (VBool true)))])
                       ])
                  ));
               (VarDec
                  [((TableAccess ("sieve", (Const (VNumber 0.)))),
                    (Const (VBool false)));
                    ((TableAccess ("sieve", (Const (VNumber 1.)))),
                     (Const (VBool false)))
                    ]);
               (ForNumerical ("i", [(Const (VNumber 0.)); (Var "upper_bound")],
                  (Block
                     [(IfElseBlock
                         [(If ((TableAccess ("sieve", (Var "i"))),
                             (Block
                                [(ForNumerical ("j",
                                    [(ArOp (Mul, (Var "i"), (Var "i")));
                                      (Var "upper_bound"); (Var "i")],
                                    (Block
                                       [(VarDec
                                           [((TableAccess ("sieve", (Var "j"))),
                                             (Const (VBool false)))])
                                         ])
                                    ))
                                  ])
                             ))
                           ])
                       ])
                  ));
               (Return (Var "sieve"))])
          ))
    
  "prime_count" -> (VNumber 25.)
  
  "sieve" -> (VTable [["1." -> (VBool false)
                
  "80." -> (VBool false)
  
  "44." -> (VBool false)
  
  "60." -> (VBool false)
  
  "23." -> (VBool true)
  
  "34." -> (VBool false)
  
  "57." -> (VBool false)
  
  "45." -> (VBool false)
  
  "96." -> (VBool false)
  
  "49." -> (VBool false)
  
  "79." -> (VBool true)
  
  "41." -> (VBool true)
  
  "51." -> (VBool false)
  
  "50." -> (VBool false)
  
  "47." -> (VBool true)
  
  "72." -> (VBool false)
  
  "33." -> (VBool false)
  
  "18." -> (VBool false)
  
  "95." -> (VBool false)
  
  "62." -> (VBool false)
  
  "84." -> (VBool false)
  
  "43." -> (VBool true)
  
  "26." -> (VBool false)
  
  "25." -> (VBool false)
  
  "74." -> (VBool false)
  
  "81." -> (VBool false)
  
  "59." -> (VBool true)
  
  "73." -> (VBool true)
  
  "94." -> (VBool false)
  
  "29." -> (VBool true)
  
  "92." -> (VBool false)
  
  "75." -> (VBool false)
  
  "69." -> (VBool false)
  
  "20." -> (VBool false)
  
  "48." -> (VBool false)
  
  "61." -> (VBool true)
  
  "86." -> (VBool false)
  
  "30." -> (VBool false)
  
  "100." -> (VBool false)
  
  "39." -> (VBool false)
  
  "97." -> (VBool true)
  
  "89." -> (VBool true)
  
  "21." -> (VBool false)
  
  "65." -> (VBool false)
  
  "66." -> (VBool false)
  
  "38." -> (VBool false)
  
  "16." -> (VBool false)
  
  "82." -> (VBool false)
  
  "68." -> (VBool false)
  
  "37." -> (VBool true)
  
  "17." -> (VBool true)
  
  "10." -> (VBool false)
  
  "7." -> (VBool true)
  
  "85." -> (VBool false)
  
  "87." -> (VBool false)
  
  "88." -> (VBool false)
  
  "19." -> (VBool true)
  
  "53." -> (VBool true)
  
  "98." -> (VBool false)
  
  "67." -> (VBool true)
  
  "27." -> (VBool false)
  
  "8." -> (VBool false)
  
  "93." -> (VBool false)
  
  "12." -> (VBool false)
  
  "46." -> (VBool false)
  
  "28." -> (VBool false)
  
  "63." -> (VBool false)
  
  "40." -> (VBool false)
  
  "77." -> (VBool false)
  
  "78." -> (VBool false)
  
  "99." -> (VBool false)
  
  "3." -> (VBool true)
  
  "13." -> (VBool true)
  
  "42." -> (VBool false)
  
  "6." -> (VBool false)
  
  "22." -> (VBool false)
  
  "35." -> (VBool false)
  
  "2." -> (VBool true)
  
  "54." -> (VBool false)
  
  "52." -> (VBool false)
  
  "14." -> (VBool false)
  
  "76." -> (VBool false)
  
  "91." -> (VBool false)
  
  "58." -> (VBool false)
  
  "36." -> (VBool false)
  
  "9." -> (VBool false)
  
  "4." -> (VBool false)
  
  "83." -> (VBool true)
  
  "70." -> (VBool false)
  
  "32." -> (VBool false)
  
  "0." -> (VBool false)
  
  "5." -> (VBool true)
  
  "90." -> (VBool false)
  
  "55." -> (VBool false)
  
  "64." -> (VBool false)
  
  "71." -> (VBool true)
  
  "31." -> (VBool true)
  
  "11." -> (VBool true)
  
  "24." -> (VBool false)
  
  "15." -> (VBool false)
  
  "56." -> (VBool false)
  
  ]]
  )
  
  ]]
  ; last_value = VNull; is_func = false; is_loop = false; jump_stmt = Default
  }

  $ ./demoFactorial.exe
  { vars =
    [["fac" ->
       (VFunction (["n"],
          (Block
             [(IfElseBlock
                 [(If ((RelOp (Leq, (Var "n"), (Const (VNumber 1.)))),
                     (Block [(Return (Const (VNumber 1.)))])))
                   ]);
               (Return
                  (ArOp (Mul,
                     (CallFunc ("fac",
                        [(ArOp (Sub, (Var "n"), (Const (VNumber 1.))))])),
                     (Var "n"))))
               ])
          ))
    
  "c" -> (VNumber 120.)
  
  ]]
  ; last_value = VNull; is_func = false; is_loop = false; jump_stmt = Default
  }
