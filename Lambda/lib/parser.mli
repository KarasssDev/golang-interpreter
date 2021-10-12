(** Main entry of parser *)
val parse : string -> (char Ast.t, string) result

type dispatch =
  { apps : dispatch -> char Ast.t Angstrom.t
  ; single : dispatch -> char Ast.t Angstrom.t
  }

(* A collection of miniparsers *)
val parse_lam : dispatch
