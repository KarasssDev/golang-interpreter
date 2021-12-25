(*  Catamorphism  *)
let%test _ =
  Tester.test_parse
    {|

let rec cata f e xs = match xs with [] -> e | x :: xs -> f x (cata f e xs);;

let isort xs =
    let rec insert x lst =
      match lst with
      | [] -> [x]
      | h :: xs -> if x < h then x :: h :: xs else h :: insert x xs in
    cata insert xs []

    |}
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
                                                (EApp (EVar "insert", EVar "x"), EVar "xs")
                                            ) ) )
                                  ] ) ) ) )
                  ]
                , EApp (EApp (EApp (EVar "cata", EVar "insert"), EVar "xs"), ENil) ) ) )
    ]
;;

(*  LCS  *)
let%test _ =
  Tester.test_parse
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
                                                    , EApp (EVar "list_len", EVar "r2") )
                                                , EVar "r1"
                                                , EVar "r2" ) ) ) )
                                  ] ) ) )
                      ]
                    , EApp (EVar "helper", ETuple [ EVar "xs"; EVar "ys" ]) ) ) ) )
    ]
;;

(*  Buggy para  *)

let%test _ =
  Tester.test_parse
    {|

  let rec para f e xs =
      match xs with [] -> e | x :: xs -> f x (xs, para f e xs)

    let isort lt xs =
      let insert3 x lst =
        para
          (fun h (tl, acc) -> if lt x h then x :: h :: tl else h :: acc)
          [x] lst in
      cata_ insert3 xs []



  |}
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
                                                        , ECons (EVar "h", EVar "acc") )
                                                    ) ) )
                                        , ECons (EVar "x", ENil) )
                                    , EVar "lst" ) ) ) )
                      ]
                    , EApp (EApp (EApp (EVar "cata_", EVar "insert3"), EVar "xs"), ENil)
                    ) ) ) )
    ]
;;

let%test _ =
  Tester.test_parse
    {|

    let ar = 2 -(7 && false ) *     3 - (2 * ( 20 || 29))


    |}
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
                , EOp (Mul, EConst (CInt 2), EOp (Or, EConst (CInt 20), EConst (CInt 29)))
                ) ) )
    ]
;;

let%test _ =
  Tester.test_parse
    {|

    let rec list_to_n = function 1 -> 1 | n -> n :: list_to_n (n - 1)

    let rec reduce f = function [] -> 1 | x :: xs -> f x (reduce f xs)

    let fact n = reduce (fun x y -> x * y) (list_to_n n)

    |}
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
                        , EApp (EVar "list_to_n", EOp (Sub, EVar "n", EConst (CInt 1))) )
                    )
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
  Tester.test_parse
    {| 

    let x = 
        let y = 2*(2*(2*(1 + 3)))::[] in 
    5 :: y

    |}
    [ DLet
        ( false
        , PVar "x"
        , ELet
            ( [ ( false
                , PVar "y"
                , ECons
                    ( EOp
                        ( Mul
                        , EConst (CInt 2)
                        , EOp
                            ( Mul
                            , EConst (CInt 2)
                            , EOp
                                ( Mul
                                , EConst (CInt 2)
                                , EOp (Add, EConst (CInt 1), EConst (CInt 3)) ) ) )
                    , ENil ) )
              ]
            , ECons (EConst (CInt 5), EVar "y") ) )
    ]
;;
