open LeanExpr

module RRange : sig
  type +'a t

  val empty : 'a t
  val length : 'a t -> int
  val append : 'a t -> 'a -> 'a t
  val get : 'a t -> int -> 'a
  val singleton : 'a -> 'a t
end

type parsing_state

val empty_state : parsing_state
val do_line : lcnt:int -> parsing_state -> string -> parsing_state * action option
val pp_state : parsing_state -> Pp.t

val pop_params : int -> expr -> (binder_kind * LeanName.t * expr) list * expr
val fix_ctor : LeanName.t -> int -> expr -> expr
val quot_name : LeanName.t
