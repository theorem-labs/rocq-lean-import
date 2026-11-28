type parsing_state

val empty_state : parsing_state

exception Refused of { state : parsing_state; error : Exninfo.iexn }
(** A recognized numbered line with the next id failed to parse. [state]
    keeps that id unavailable, so that later ids stay in sequence. *)

val do_line : lcnt:int -> parsing_state -> string ->
  parsing_state * LeanExpr.action option

val pp_state : parsing_state -> Pp.t
