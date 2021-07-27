(** Real monadic interpreter goes here *)

open Base
open Utils

module Interpret (M : MONAD_FAIL) : sig
  val run : Ast.t -> (int, Utils.error) M.t
end = struct
  let run _ =
    (* implement interpreter here *)
    if true then M.error (UnknownVariable "var") else failwith "not implemented"
end

let parse_and_run str =
  let ans =
    let module I = Interpret (Result) in
    let open Result.Syntax in
    let* ast = Parser.parse str in
    I.run ast in
  ans
