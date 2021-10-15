Lua tables tests

  $ ./demoTable.exe
  { vars =
    [["foo" -> (VFunction ([], (Block [(Return (Const (VString "FOO")))])))
    
  "table_with_expr_key" -> (VTable [[(VNumber 10.) -> (VNumber 5.)
                              
  (VNumber 1.) -> (VNumber 5.)
  
  (VNumber 17.) -> (VNumber 20.)
  
  ]]
  )
  
  "table_mixed" -> (VTable [[(VNumber 2.) -> (VNumber 3.)
                      
  (VString "foo") -> (VString "poo")
  
  (VNumber 9.) -> (VNumber 9.)
  
  (VNumber 14.) -> (VNumber 5.)
  
  (VNumber 1.) -> (VNumber 1.)
  
  ]]
  )
  
  "table_with_name_key" -> (VTable [[(VString "a") -> (VNumber 5.)
                              
  (VString "foo") -> (VNumber 15.)
  
  ]]
  )
  
  "sample_int_key" -> (VNumber 10.)
  
  ]]
  ; last_value = VNull; is_func = false; is_loop = false; jump_stmt = Default
  }
  $ ./demoNullKeyTable.exe
  Error: Table index can't be nil
