open LeanExpr

module RRange : sig
  type +'a t
  (** Like Range.t, but instead of cons we append *)

  val empty : 'a t
  val length : 'a t -> int
  val append : 'a t -> 'a -> 'a t
  val get : 'a t -> int -> 'a
  (** [get r i] is the [i]th value appended, from 0; [Not_found] when [i] is
      negative or not below [length r]. *)

  val singleton : 'a -> 'a t
end

val pop_params : int -> expr -> (binder_kind * LeanName.t * expr) list * expr
val fix_ctor : LeanName.t -> int -> expr -> expr
val quot_name : LeanName.t

val nat_lit : Z.t -> expr
(** [nat_lit z], [z] non-negative: the literal [Nat] of the decimal string [Z.to_string z], so that equal values
    give equal expressions ("007", "7" and 7 alike). Every writer of a [Nat] builds it here; why it is a string is
    stated at [lean_obj] in lean.ml. *)
