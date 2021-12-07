open Tester

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
                        , [ (PList [], EVar "e")
                          ; ( PCons (PVar "x", PVar "xs")
                            , EApp
                                ( EApp (EVar "f", EVar "x")
                                , EApp
                                    ( EApp
                                        (EApp (EVar "cata", EVar "f"), EVar "e")
                                    , EVar "xs" ) ) ) ] ) ) ) ) )
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
                                , [ (PList [], EList [EVar "x"])
                                  ; ( PCons (PVar "h", PVar "xs")
                                    , EIf
                                        ( EOp (Less, EVar "x", EVar "h")
                                        , ECons
                                            ( EVar "x"
                                            , ECons (EVar "h", EVar "xs") )
                                        , ECons
                                            ( EVar "h"
                                            , EApp
                                                ( EApp (EVar "insert", EVar "x")
                                                , EVar "xs" ) ) ) ) ] ) ) ) ) ]
                , EApp
                    ( EApp (EApp (EVar "cata", EVar "insert"), EVar "xs")
                    , EList [] ) ) ) ) ]

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
                                , [ (PTuple [PList []; PWild], EList [])
                                  ; (PTuple [PWild; PList []], EList [])
                                  ; ( PTuple
                                        [ PCons (PVar "x", PVar "xs")
                                        ; PCons (PVar "y", PVar "ys") ]
                                    , EIf
                                        ( EOp (Eq, EVar "x", EVar "y")
                                        , ECons
                                            ( EVar "x"
                                            , EApp
                                                ( EVar "helper"
                                                , ETuple [EVar "xs"; EVar "ys"]
                                                ) )
                                        , ELet
                                            ( [ ( false
                                                , PVar "r1"
                                                , EApp
                                                    ( EVar "helper"
                                                    , ETuple
                                                        [ ECons
                                                            (EVar "x", EVar "xs")
                                                        ; EVar "ys" ] ) )
                                              ; ( false
                                                , PVar "r2"
                                                , EApp
                                                    ( EVar "helper"
                                                    , ETuple
                                                        [ EVar "xs"
                                                        ; ECons
                                                            (EVar "y", EVar "ys")
                                                        ] ) ) ]
                                            , EIf
                                                ( EOp
                                                    ( Gre
                                                    , EApp
                                                        ( EVar "list_len"
                                                        , EVar "r1" )
                                                    , EApp
                                                        ( EVar "list_len"
                                                        , EVar "r2" ) )
                                                , EVar "r1"
                                                , EVar "r2" ) ) ) ) ] ) ) ) ]
                    , EApp (EVar "helper", ETuple [EVar "xs"; EVar "ys"]) ) ) )
        ) ]

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
                        , [ (PList [], EVar "e")
                          ; ( PCons (PVar "x", PVar "xs")
                            , EApp
                                ( EApp (EVar "f", EVar "x")
                                , ETuple
                                    [ EVar "xs"
                                    ; EApp
                                        ( EApp
                                            ( EApp (EVar "para", EVar "f")
                                            , EVar "e" )
                                        , EVar "xs" ) ] ) ) ] ) ) ) ) )
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
                                                    ( PTuple
                                                        [PVar "tl"; PVar "acc"]
                                                    , EIf
                                                        ( EApp
                                                            ( EApp
                                                                ( EVar "lt"
                                                                , EVar "x" )
                                                            , EVar "h" )
                                                        , ECons
                                                            ( EVar "x"
                                                            , ECons
                                                                ( EVar "h"
                                                                , EVar "tl" ) )
                                                        , ECons
                                                            ( EVar "h"
                                                            , EVar "acc" ) ) )
                                                ) )
                                        , EList [EVar "x"] )
                                    , EVar "lst" ) ) ) ) ]
                    , EApp
                        ( EApp (EApp (EVar "cata_", EVar "insert3"), EVar "xs")
                        , EList [] ) ) ) ) ) ]
