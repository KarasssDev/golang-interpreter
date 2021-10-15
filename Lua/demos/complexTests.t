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
                         [((TableAccess ("sieve", [(Var "i")])),
                           (Const (VBool true)))])
                       ])
                  ));
               (VarDec
                  [((TableAccess ("sieve", [(Const (VNumber 0.))])),
                    (Const (VBool false)));
                    ((TableAccess ("sieve", [(Const (VNumber 1.))])),
                     (Const (VBool false)))
                    ]);
               (ForNumerical ("i", [(Const (VNumber 0.)); (Var "upper_bound")],
                  (Block
                     [(IfStatement (
                         ((TableAccess ("sieve", [(Var "i")])),
                          (Block
                             [(ForNumerical ("j",
                                 [(ArOp (Mul, (Var "i"), (Var "i")));
                                   (Var "upper_bound"); (Var "i")],
                                 (Block
                                    [(VarDec
                                        [((TableAccess ("sieve", [(Var "j")])),
                                          (Const (VBool false)))])
                                      ])
                                 ))
                               ])),
                         [], None))
                       ])
                  ));
               (Return (Var "sieve"))])
          ))
    
  "prime_count" -> (VNumber 25.)
  
  "sieve" -> (VTable [[(VNumber 34.) -> (VBool false)
                
  (VNumber 15.) -> (VBool false)
  
  (VNumber 68.) -> (VBool false)
  
  (VNumber 64.) -> (VBool false)
  
  (VNumber 99.) -> (VBool false)
  
  (VNumber 35.) -> (VBool false)
  
  (VNumber 74.) -> (VBool false)
  
  (VNumber 70.) -> (VBool false)
  
  (VNumber 66.) -> (VBool false)
  
  (VNumber 20.) -> (VBool false)
  
  (VNumber 16.) -> (VBool false)
  
  (VNumber 46.) -> (VBool false)
  
  (VNumber 2.) -> (VBool true)
  
  (VNumber 100.) -> (VBool false)
  
  (VNumber 71.) -> (VBool true)
  
  (VNumber 85.) -> (VBool false)
  
  (VNumber 81.) -> (VBool false)
  
  (VNumber 29.) -> (VBool true)
  
  (VNumber 97.) -> (VBool true)
  
  (VNumber 91.) -> (VBool false)
  
  (VNumber 76.) -> (VBool false)
  
  (VNumber 13.) -> (VBool true)
  
  (VNumber 41.) -> (VBool true)
  
  (VNumber 89.) -> (VBool true)
  
  (VNumber 96.) -> (VBool false)
  
  (VNumber 58.) -> (VBool false)
  
  (VNumber 37.) -> (VBool true)
  
  (VNumber 47.) -> (VBool true)
  
  (VNumber 98.) -> (VBool false)
  
  (VNumber 51.) -> (VBool false)
  
  (VNumber 56.) -> (VBool false)
  
  (VNumber 5.) -> (VBool true)
  
  (VNumber 32.) -> (VBool false)
  
  (VNumber 7.) -> (VBool true)
  
  (VNumber 43.) -> (VBool true)
  
  (VNumber 57.) -> (VBool false)
  
  (VNumber 21.) -> (VBool false)
  
  (VNumber 95.) -> (VBool false)
  
  (VNumber 83.) -> (VBool true)
  
  (VNumber 63.) -> (VBool false)
  
  (VNumber 65.) -> (VBool false)
  
  (VNumber 44.) -> (VBool false)
  
  (VNumber 93.) -> (VBool false)
  
  (VNumber 87.) -> (VBool false)
  
  (VNumber 55.) -> (VBool false)
  
  (VNumber 19.) -> (VBool true)
  
  (VNumber 52.) -> (VBool false)
  
  (VNumber 60.) -> (VBool false)
  
  (VNumber 27.) -> (VBool false)
  
  (VNumber 9.) -> (VBool false)
  
  (VNumber 28.) -> (VBool false)
  
  (VNumber 12.) -> (VBool false)
  
  (VNumber 42.) -> (VBool false)
  
  (VNumber 31.) -> (VBool true)
  
  (VNumber 3.) -> (VBool true)
  
  (VNumber 61.) -> (VBool true)
  
  (VNumber 84.) -> (VBool false)
  
  (VNumber 48.) -> (VBool false)
  
  (VNumber 49.) -> (VBool false)
  
  (VNumber 72.) -> (VBool false)
  
  (VNumber 36.) -> (VBool false)
  
  (VNumber 10.) -> (VBool false)
  
  (VNumber 79.) -> (VBool true)
  
  (VNumber 8.) -> (VBool false)
  
  (VNumber 78.) -> (VBool false)
  
  (VNumber 25.) -> (VBool false)
  
  (VNumber 82.) -> (VBool false)
  
  (VNumber 33.) -> (VBool false)
  
  (VNumber 73.) -> (VBool true)
  
  (VNumber 23.) -> (VBool true)
  
  (VNumber 59.) -> (VBool true)
  
  (VNumber 86.) -> (VBool false)
  
  (VNumber 53.) -> (VBool true)
  
  (VNumber 80.) -> (VBool false)
  
  (VNumber 6.) -> (VBool false)
  
  (VNumber 69.) -> (VBool false)
  
  (VNumber 92.) -> (VBool false)
  
  (VNumber 14.) -> (VBool false)
  
  (VNumber 38.) -> (VBool false)
  
  (VNumber 1.) -> (VBool false)
  
  (VNumber 77.) -> (VBool false)
  
  (VNumber 90.) -> (VBool false)
  
  (VNumber 17.) -> (VBool true)
  
  (VNumber 67.) -> (VBool true)
  
  (VNumber 50.) -> (VBool false)
  
  (VNumber 62.) -> (VBool false)
  
  (VNumber 39.) -> (VBool false)
  
  (VNumber 24.) -> (VBool false)
  
  (VNumber 88.) -> (VBool false)
  
  (VNumber 54.) -> (VBool false)
  
  (VNumber 94.) -> (VBool false)
  
  (VNumber 18.) -> (VBool false)
  
  (VNumber 30.) -> (VBool false)
  
  (VNumber 0.) -> (VBool false)
  
  (VNumber 45.) -> (VBool false)
  
  (VNumber 26.) -> (VBool false)
  
  (VNumber 11.) -> (VBool true)
  
  (VNumber 22.) -> (VBool false)
  
  (VNumber 75.) -> (VBool false)
  
  (VNumber 4.) -> (VBool false)
  
  (VNumber 40.) -> (VBool false)
  
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
             [(IfStatement (
                 ((RelOp (Leq, (Var "n"), (Const (VNumber 1.)))),
                  (Block [(Return (Const (VNumber 1.)))])),
                 [], None));
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
