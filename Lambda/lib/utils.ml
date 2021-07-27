open Base
open Ast

(* TODO: use a set instead of list *)
let list_remove x = List.filter ~f:(fun a -> not (String.equal a x))

let free_vars =
  let rec helper acc = function
    | Var s -> s :: acc
    | Abs (s, l) -> acc @ list_remove s (helper [] l)
    | App (l, r) -> helper (helper acc r) l in
  helper []

let is_free_in x term = List.mem (free_vars term) x ~equal:String.equal

type error =
  | UnknownVariable of string  (** just for example *)
  | ParsingErrorDescription

module type MONAD_FAIL = sig
  include Base.Monad.S2

  val error : 'e -> ('a, 'e) t
end

module Result : sig
  type ('a, 'e) t = ('a, 'e) Result.t

  include MONAD_FAIL with type ('a, 'e) t := ('a, 'e) t

  module Syntax : sig
    (* Monad *)
    val ( let* ) : ('a, 'e) t -> ('a -> ('b, 'e) t) -> ('b, 'e) t
  end
end = struct
  include Base.Result

  type ('a, 'e) t = ('a, 'e) Result.t

  let error msg = Error msg

  module Syntax = struct let ( let* ) x f = bind x ~f end
end
