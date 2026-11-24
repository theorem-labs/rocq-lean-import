open LeanExpr

type parsing_state

type path = Legacy | New
(** The path an export takes: [New] for Lean 4.17.0 and later, read
    from the metadata [lean.version]; [Legacy] for an earlier version, for an
    unreadable or absent version (with a warning), and before any metadata. *)

val path : parsing_state -> path
(** The path the first metadata line of the export chose. *)

val version : parsing_state -> (int * int * int) option
(** The Lean version [(MAJOR, MINOR, PATCH)] the first metadata line of the
    export gave in [lean.version] (a leading [v] and a suffix after [-] left
    out); [None] before any metadata, and when that version cannot be read. *)

exception Refused of {
  state : parsing_state;
  entry : LeanName.t option;
  error : Exninfo.iexn;
}
(** [do_line] and [do_prefix_line] raise [Refused] for a line they cannot
    parse: [error] is why, [entry] the name of the entry the line declares when
    it was read before [error], and [state] the state to read the next line
    with. A refused name, level or expression line whose id was the next one
    leaves a placeholder for that id in [state], so that the ids after it stay
    in sequence; a line that uses the id is refused in turn. *)

val empty_state : parsing_state
val is_ndjson_line : string -> bool

val do_prefix_line : lcnt:int -> parsing_state -> string -> parsing_state
(** Read a line before the first line to import: its names, levels and
    expressions only; a declaration is skipped without being parsed. *)

val do_line : lcnt:int -> parsing_state -> string -> parsing_state * action option
val pp_state : parsing_state -> Pp.t
