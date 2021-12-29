open Parser
open Tester

let%test _ =
  test_parse
    ~label:"Non-tailrec List map"
    ~code:
      {|

    let rec map f l = match l with [] -> [] | hd :: tl -> f hd :: map f tl

    |}
    ~expected:
      [ DLet
          ( true
          , PVar "map"
          , EFun
              ( PVar "f"
              , EFun
                  ( PVar "l"
                  , EMatch
                      ( EVar "l"
                      , [ PNil, ENil
                        ; ( PCons (PVar "hd", PVar "tl")
                          , ECons
                              ( EApp (EVar "f", EVar "hd")
                              , EApp (EApp (EVar "map", EVar "f"), EVar "tl") ) )
                        ] ) ) ) )
      ]
;;

let%test _ =
  test_parse
    ~label:"Tailrec fold_left"
    ~code:
      {|

    let rec fold_left f init = function 
    | [] -> init 
    | hd :: tl -> fold_left f (f init hd) tl

    |}
    ~expected:
      [ DLet
          ( true
          , PVar "fold_left"
          , EFun
              ( PVar "f"
              , EFun
                  ( PVar "init"
                  , EFun
                      ( PVar "match"
                      , EMatch
                          ( EVar "match"
                          , [ PNil, EVar "init"
                            ; ( PCons (PVar "hd", PVar "tl")
                              , EApp
                                  ( EApp
                                      ( EApp (EVar "fold_left", EVar "f")
                                      , EApp (EApp (EVar "f", EVar "init"), EVar "hd") )
                                  , EVar "tl" ) )
                            ] ) ) ) ) )
      ]
;;

let%test _ =
  test_parse
    ~label:"Dirty arithmetic"
    ~code:{|

    let _ = 4 / (1 + 1) :: 2*(2 + (2 - 3)) / 5 :: f x

    |}
    ~expected:
      [ DLet
          ( false
          , PWild
          , ECons
              ( EOp (Div, EConst (CInt 4), EOp (Add, EConst (CInt 1), EConst (CInt 1)))
              , ECons
                  ( EOp
                      ( Mul
                      , EConst (CInt 2)
                      , EOp
                          ( Div
                          , EOp
                              ( Add
                              , EConst (CInt 2)
                              , EOp (Sub, EConst (CInt 2), EConst (CInt 3)) )
                          , EConst (CInt 5) ) )
                  , EApp (EVar "f", EVar "x") ) ) )
      ]
;;

let%test _ =
  test_parse
    ~label:"Nested let-experssions"
    ~code:
      {|

    let a = 
      let b = 
        let c = 
          let d x = x + 1 
        in d 
      in c
      in fun x -> b (x / 2)

    |}
    ~expected:
      [ DLet
          ( false
          , PVar "a"
          , ELet
              ( [ ( false
                  , PVar "b"
                  , ELet
                      ( [ ( false
                          , PVar "c"
                          , ELet
                              ( [ ( false
                                  , PVar "d"
                                  , EFun (PVar "x", EOp (Add, EVar "x", EConst (CInt 1)))
                                  )
                                ]
                              , EVar "d" ) )
                        ]
                      , EVar "c" ) )
                ]
              , EFun (PVar "x", EApp (EVar "b", EOp (Div, EVar "x", EConst (CInt 2)))) )
          )
      ]
;;

let%test _ =
  test_parse
    ~label:"Long whitespaces"
    ~code:
      {|

    let   rec
       fibonacci    n  =

      if n <= 1  then n else 

      fibonacci
      (n - 1)   +
            fibonacci (n - 2)

    |}
    ~expected:
      [ DLet
          ( true
          , PVar "fibonacci"
          , EFun
              ( PVar "n"
              , EIf
                  ( EOp (Leq, EVar "n", EConst (CInt 1))
                  , EVar "n"
                  , EOp
                      ( Add
                      , EApp (EVar "fibonacci", EOp (Sub, EVar "n", EConst (CInt 1)))
                      , EApp (EVar "fibonacci", EOp (Sub, EVar "n", EConst (CInt 2))) ) )
              ) )
      ]
;;

let%test _ =
  test_parse
    ~label:"Effect handling"
    ~code:
      {|

      effect E : string -> int;;

      let to_str = function "0" -> 0 | "1" -> 1 | s -> perform (E s)
      ;;

      let rec sum_strs = function 
      | [] -> 0 
      | hd :: tl -> to_str hd + sum_strs tl;;


      let result = match sum_strs ["10"; "1"; "abc"; "0"] with 
      | effect (E s) k  -> continue k 0
      | res -> res
      ;;



    |}
    ~expected:
      [ DEffect2 ("E", TString, TInt)
      ; DLet
          ( false
          , PVar "to_str"
          , EFun
              ( PVar "match"
              , EMatch
                  ( EVar "match"
                  , [ PConst (CString "0"), EConst (CInt 0)
                    ; PConst (CString "1"), EConst (CInt 1)
                    ; PVar "s", EPerform (EEffect2 ("E", EVar "s"))
                    ] ) ) )
      ; DLet
          ( true
          , PVar "sum_strs"
          , EFun
              ( PVar "match"
              , EMatch
                  ( EVar "match"
                  , [ PNil, EConst (CInt 0)
                    ; ( PCons (PVar "hd", PVar "tl")
                      , EOp
                          ( Add
                          , EApp (EVar "to_str", EVar "hd")
                          , EApp (EVar "sum_strs", EVar "tl") ) )
                    ] ) ) )
      ; DLet
          ( false
          , PVar "result"
          , EMatch
              ( EApp
                  ( EVar "sum_strs"
                  , ECons
                      ( EConst (CString "10")
                      , ECons
                          ( EConst (CString "1")
                          , ECons
                              (EConst (CString "abc"), ECons (EConst (CString "0"), ENil))
                          ) ) )
              , [ ( PEffectH (PEffect2 ("E", PVar "s"), "k")
                  , EContinue ("k", EConst (CInt 0)) )
                ; PVar "res", EVar "res"
                ] ) )
      ]
;;

let%test _ =
  test_parse
    ~label:"Pattern matching in declaration"
    ~code:
      {|

      let (((e, s))) = 2, 2;;

      let rest :: [] = (e, s) :: [];;


      let (t, u, p, (l, (e, s))) = 1, 2, 3, (3, rest);;

      |}
    ~expected:
      [ DLet
          ( false
          , PTuple [ PVar "e"; PVar "s" ]
          , ETuple [ EConst (CInt 2); EConst (CInt 2) ] )
      ; DLet
          (false, PCons (PVar "rest", PNil), ECons (ETuple [ EVar "e"; EVar "s" ], ENil))
      ; DLet
          ( false
          , PTuple
              [ PVar "t"
              ; PVar "u"
              ; PVar "p"
              ; PTuple [ PVar "l"; PTuple [ PVar "e"; PVar "s" ] ]
              ]
          , ETuple
              [ EConst (CInt 1)
              ; EConst (CInt 2)
              ; EConst (CInt 3)
              ; ETuple [ EConst (CInt 3); EVar "rest" ]
              ] )
      ]
;;

let%test _ =
  test_parse
    ~label:"Catamorphism"
    ~code:
      {|

    let rec cata f e xs = match xs with [] -> e | x :: xs -> f x (cata f e xs);;

    let isort xs =
    let rec insert x lst =
      match lst with
      | [] -> [x]
      | h :: xs -> if x < h then x :: h :: xs else h :: insert x xs in
    cata insert xs []

    |}
    ~expected:
      [ DLet
          ( true
          , PVar "cata"
          , EFun
              ( PVar "f"
              , EFun
                  ( PVar "e"
                  , EFun
                      ( PVar "xs"
                      , EMatch
                          ( EVar "xs"
                          , [ PNil, EVar "e"
                            ; ( PCons (PVar "x", PVar "xs")
                              , EApp
                                  ( EApp (EVar "f", EVar "x")
                                  , EApp
                                      ( EApp (EApp (EVar "cata", EVar "f"), EVar "e")
                                      , EVar "xs" ) ) )
                            ] ) ) ) ) )
      ; DLet
          ( false
          , PVar "isort"
          , EFun
              ( PVar "xs"
              , ELet
                  ( [ ( true
                      , PVar "insert"
                      , EFun
                          ( PVar "x"
                          , EFun
                              ( PVar "lst"
                              , EMatch
                                  ( EVar "lst"
                                  , [ PNil, ECons (EVar "x", ENil)
                                    ; ( PCons (PVar "h", PVar "xs")
                                      , EIf
                                          ( EOp (Less, EVar "x", EVar "h")
                                          , ECons (EVar "x", ECons (EVar "h", EVar "xs"))
                                          , ECons
                                              ( EVar "h"
                                              , EApp
                                                  ( EApp (EVar "insert", EVar "x")
                                                  , EVar "xs" ) ) ) )
                                    ] ) ) ) )
                    ]
                  , EApp (EApp (EApp (EVar "cata", EVar "insert"), EVar "xs"), ENil) ) )
          )
      ]
;;

let%test _ =
  test_parse
    ~label:"LCS"
    ~code:
      {| 

    let lcs xs ys =
    let rec helper = function
      | [], _ -> []
      | _, [] -> []
      | x :: xs, y :: ys -> 
      if x = y 
      then x :: helper (xs, ys)
      else 
          (let r1 = helper (x :: xs, ys) in
          let r2 = helper (xs, y :: ys) in
          if list_len r1 > list_len r2 then r1 else r2)
    in
    helper (xs, ys)


    |}
    ~expected:
      [ DLet
          ( false
          , PVar "lcs"
          , EFun
              ( PVar "xs"
              , EFun
                  ( PVar "ys"
                  , ELet
                      ( [ ( true
                          , PVar "helper"
                          , EFun
                              ( PVar "match"
                              , EMatch
                                  ( EVar "match"
                                  , [ PTuple [ PNil; PWild ], ENil
                                    ; PTuple [ PWild; PNil ], ENil
                                    ; ( PTuple
                                          [ PCons (PVar "x", PVar "xs")
                                          ; PCons (PVar "y", PVar "ys")
                                          ]
                                      , EIf
                                          ( EOp (Eq, EVar "x", EVar "y")
                                          , ECons
                                              ( EVar "x"
                                              , EApp
                                                  ( EVar "helper"
                                                  , ETuple [ EVar "xs"; EVar "ys" ] ) )
                                          , ELet
                                              ( [ ( false
                                                  , PVar "r1"
                                                  , EApp
                                                      ( EVar "helper"
                                                      , ETuple
                                                          [ ECons (EVar "x", EVar "xs")
                                                          ; EVar "ys"
                                                          ] ) )
                                                ; ( false
                                                  , PVar "r2"
                                                  , EApp
                                                      ( EVar "helper"
                                                      , ETuple
                                                          [ EVar "xs"
                                                          ; ECons (EVar "y", EVar "ys")
                                                          ] ) )
                                                ]
                                              , EIf
                                                  ( EOp
                                                      ( Gre
                                                      , EApp (EVar "list_len", EVar "r1")
                                                      , EApp (EVar "list_len", EVar "r2")
                                                      )
                                                  , EVar "r1"
                                                  , EVar "r2" ) ) ) )
                                    ] ) ) )
                        ]
                      , EApp (EVar "helper", ETuple [ EVar "xs"; EVar "ys" ]) ) ) ) )
      ]
;;

let%test _ =
  test_parse
    ~label:"Paramorphism"
    ~code:
      {|

  let rec para f e xs =
      match xs with [] -> e | x :: xs -> f x (xs, para f e xs)
    ;;

    let isort lt xs =
      let insert3 x lst =
        para
          (fun h (tl, acc) -> if lt x h then x :: h :: tl else h :: acc)
          [x] lst in
      cata_ insert3 xs []



  |}
    ~expected:
      [ DLet
          ( true
          , PVar "para"
          , EFun
              ( PVar "f"
              , EFun
                  ( PVar "e"
                  , EFun
                      ( PVar "xs"
                      , EMatch
                          ( EVar "xs"
                          , [ PNil, EVar "e"
                            ; ( PCons (PVar "x", PVar "xs")
                              , EApp
                                  ( EApp (EVar "f", EVar "x")
                                  , ETuple
                                      [ EVar "xs"
                                      ; EApp
                                          ( EApp (EApp (EVar "para", EVar "f"), EVar "e")
                                          , EVar "xs" )
                                      ] ) )
                            ] ) ) ) ) )
      ; DLet
          ( false
          , PVar "isort"
          , EFun
              ( PVar "lt"
              , EFun
                  ( PVar "xs"
                  , ELet
                      ( [ ( false
                          , PVar "insert3"
                          , EFun
                              ( PVar "x"
                              , EFun
                                  ( PVar "lst"
                                  , EApp
                                      ( EApp
                                          ( EApp
                                              ( EVar "para"
                                              , EFun
                                                  ( PVar "h"
                                                  , EFun
                                                      ( PTuple [ PVar "tl"; PVar "acc" ]
                                                      , EIf
                                                          ( EApp
                                                              ( EApp (EVar "lt", EVar "x")
                                                              , EVar "h" )
                                                          , ECons
                                                              ( EVar "x"
                                                              , ECons (EVar "h", EVar "tl")
                                                              )
                                                          , ECons (EVar "h", EVar "acc")
                                                          ) ) ) )
                                          , ECons (EVar "x", ENil) )
                                      , EVar "lst" ) ) ) )
                        ]
                      , EApp (EApp (EApp (EVar "cata_", EVar "insert3"), EVar "xs"), ENil)
                      ) ) ) )
      ]
;;

let%test _ =
  test_parse
    ~label:"Effect matching"
    ~code:
      {|

      effect E1: string;;

       effect E2: int -> string eff;;

      let res = match E1 with 
      | E2 n -> 0
      | E1 -> 1



      |}
    ~expected:
      [ DEffect1 ("E1", TString)
      ; DEffect2 ("E2", TInt, TEffect TString)
      ; DLet
          ( false
          , PVar "res"
          , EMatch
              ( EEffect1 "E1"
              , [ PEffect2 ("E2", PVar "n"), EConst (CInt 0)
                ; PEffect1 "E1", EConst (CInt 1)
                ] ) )
      ]
;;

let%test _ =
  test_parse
    ~label:"Arithm with whitespaces"
    ~code:{|

    let ar = 2 -(7 && false ) *     3 - (2 * ( 20 || 29))

    |}
    ~expected:
      [ DLet
          ( false
          , PVar "ar"
          , EOp
              ( Sub
              , EConst (CInt 2)
              , EOp
                  ( Sub
                  , EOp
                      ( Mul
                      , EOp (And, EConst (CInt 7), EConst (CBool false))
                      , EConst (CInt 3) )
                  , EOp
                      (Mul, EConst (CInt 2), EOp (Or, EConst (CInt 20), EConst (CInt 29)))
                  ) ) )
      ]
;;

let%test _ =
  test_parse
    ~label:"Lambdas"
    ~code:
      {|

    let rec list_to_n = function 1 -> 1 | n -> n :: list_to_n (n - 1);;

    let rec reduce f = function [] -> 1 | x :: xs -> f x (reduce f xs);;

    let fact n = reduce (fun x y -> x * y) (list_to_n n)

    |}
    ~expected:
      [ DLet
          ( true
          , PVar "list_to_n"
          , EFun
              ( PVar "match"
              , EMatch
                  ( EVar "match"
                  , [ PConst (CInt 1), EConst (CInt 1)
                    ; ( PVar "n"
                      , ECons
                          ( EVar "n"
                          , EApp (EVar "list_to_n", EOp (Sub, EVar "n", EConst (CInt 1)))
                          ) )
                    ] ) ) )
      ; DLet
          ( true
          , PVar "reduce"
          , EFun
              ( PVar "f"
              , EFun
                  ( PVar "match"
                  , EMatch
                      ( EVar "match"
                      , [ PNil, EConst (CInt 1)
                        ; ( PCons (PVar "x", PVar "xs")
                          , EApp
                              ( EApp (EVar "f", EVar "x")
                              , EApp (EApp (EVar "reduce", EVar "f"), EVar "xs") ) )
                        ] ) ) ) )
      ; DLet
          ( false
          , PVar "fact"
          , EFun
              ( PVar "n"
              , EApp
                  ( EApp
                      ( EVar "reduce"
                      , EFun (PVar "x", EFun (PVar "y", EOp (Mul, EVar "x", EVar "y"))) )
                  , EApp (EVar "list_to_n", EVar "n") ) ) )
      ]
;;

let%test _ =
  test_parse
    ~label:"Effect cons with one arg"
    ~code:
      {|

    effect O    : (int -> int)  

    ;;

    let f = fun x -> x + 1  ;;

    let res = O f

    |}
    ~expected:
      [ DEffect1 ("O", TArrow (TInt, TInt))
      ; DLet (false, PVar "f", EFun (PVar "x", EOp (Add, EVar "x", EConst (CInt 1))))
      ; DLet (false, PVar "res", EEffect2 ("O", EVar "f"))
      ]
;;

let%test _ =
  test_parse
    ~label:"Effect cons with two args"
    ~code:
      {|

    effect O    : (int -> int) -> string 
    ;;

    let e = O (fun e -> e * e)

    |}
    ~expected:
      [ DEffect2 ("O", TArrow (TInt, TInt), TString)
      ; DLet
          (false, PVar "e", EEffect2 ("O", EFun (PVar "e", EOp (Mul, EVar "e", EVar "e"))))
      ]
;;

let%test _ =
  test_parse
    ~label:"Matrix sum"
    ~code:
      {|


      let s = read_line ;;
    let matrix1 = map (fun s -> to_int s) (split_by " " s);;
    let s2 = read_line ;;


    let   matrix2 
    = map (fun s -> to_int s) (split_by " " s);;

    let m_sum =
      let list_sum = function 
      | [], [] -> []
      | hd1 :: tl1, hd2 :: tl2 -> (hd1 + hd2) :: (list_sum (tl1, tl2))
      | _ -> throw error
       in 
       function 
       | l1 :: rest1, l2 :: rest2 -> (list_sum (l1, l2)) :: (m_sum (rest1, rest2))
       | [], [] -> []
       | _ -> throw error


    |}
    ~expected:
      [ DLet (false, PVar "s", EVar "read_line")
      ; DLet
          ( false
          , PVar "matrix1"
          , EApp
              ( EApp (EVar "map", EFun (PVar "s", EApp (EVar "to_int", EVar "s")))
              , EApp (EApp (EVar "split_by", EConst (CString " ")), EVar "s") ) )
      ; DLet (false, PVar "s2", EVar "read_line")
      ; DLet
          ( false
          , PVar "matrix2"
          , EApp
              ( EApp (EVar "map", EFun (PVar "s", EApp (EVar "to_int", EVar "s")))
              , EApp (EApp (EVar "split_by", EConst (CString " ")), EVar "s") ) )
      ; DLet
          ( false
          , PVar "m_sum"
          , ELet
              ( [ ( false
                  , PVar "list_sum"
                  , EFun
                      ( PVar "match"
                      , EMatch
                          ( EVar "match"
                          , [ PTuple [ PNil; PNil ], ENil
                            ; ( PTuple
                                  [ PCons (PVar "hd1", PVar "tl1")
                                  ; PCons (PVar "hd2", PVar "tl2")
                                  ]
                              , ECons
                                  ( EOp (Add, EVar "hd1", EVar "hd2")
                                  , EApp
                                      (EVar "list_sum", ETuple [ EVar "tl1"; EVar "tl2" ])
                                  ) )
                            ; PWild, EApp (EVar "throw", EVar "error")
                            ] ) ) )
                ]
              , EFun
                  ( PVar "match"
                  , EMatch
                      ( EVar "match"
                      , [ ( PTuple
                              [ PCons (PVar "l1", PVar "rest1")
                              ; PCons (PVar "l2", PVar "rest2")
                              ]
                          , ECons
                              ( EApp (EVar "list_sum", ETuple [ EVar "l1"; EVar "l2" ])
                              , EApp (EVar "m_sum", ETuple [ EVar "rest1"; EVar "rest2" ])
                              ) )
                        ; PTuple [ PNil; PNil ], ENil
                        ; PWild, EApp (EVar "throw", EVar "error")
                        ] ) ) ) )
      ]
;;

let%test _ =
  test_parse
    ~label:"Fixpoint"
    ~code:
      {|


     let rec fix f x = f (fix f) x
     ;;
    let fac f n = if n <= 1 then 1 else f (n - 1) * n;;
    let fact = fix fac;;
    let res = fact 10;;


    |}
    ~expected:
      [ DLet
          ( true
          , PVar "fix"
          , EFun
              ( PVar "f"
              , EFun
                  (PVar "x", EApp (EApp (EVar "f", EApp (EVar "fix", EVar "f")), EVar "x"))
              ) )
      ; DLet
          ( false
          , PVar "fac"
          , EFun
              ( PVar "f"
              , EFun
                  ( PVar "n"
                  , EIf
                      ( EOp (Leq, EVar "n", EConst (CInt 1))
                      , EConst (CInt 1)
                      , EOp
                          ( Mul
                          , EApp (EVar "f", EOp (Sub, EVar "n", EConst (CInt 1)))
                          , EVar "n" ) ) ) ) )
      ; DLet (false, PVar "fact", EApp (EVar "fix", EVar "fac"))
      ; DLet (false, PVar "res", EApp (EVar "fact", EConst (CInt 10)))
      ]
;;
