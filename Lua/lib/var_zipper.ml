(* === Utility functions === *)

open Ast

let var_zipper l1 l2 =
  let rec helper l1 l2 acc =
    match (l1, l2) with
    | [], [] -> acc
    | hd1 :: tl1, hd2 :: tl2 -> (hd1, hd2) :: helper tl1 tl2 acc
    | hd1 :: tl1, [] -> (hd1, Const VNull) :: helper tl1 [] acc
    | [], _ :: _ -> acc in
  helper l1 l2 []
