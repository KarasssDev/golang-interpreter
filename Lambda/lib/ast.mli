(** Names are strings because we use default representation *)
type name = string

(** The main type for our AST (дерева абстрактного синтаксиса) *)
type t =
  | Var of name  (** Variable [x] *)
  | Abs of name * t  (** Abstraction [λx.t] *)
  | App of t * t  (** Application [f x] *)
