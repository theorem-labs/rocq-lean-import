
module U : sig
  type t = Prop | Succ of t | Max of t * t | IMax of t * t | UNamed of LeanName.t
end

type binder_kind =
  | NotImplicit
  | Maximal
  | NonMaximal
  | Typeclass  (** WRT Coq, Typeclass is like Maximal. *)

type expr =
  | Bound of int
  | Sort of U.t
  | Const of LeanName.t * U.t list
  | App of expr * expr
  | Let of { name : LeanName.t; ty : expr; v : expr; rest : expr }
      (** Let: undocumented in export_format.md *)
  | Lam of binder_kind * LeanName.t * expr * expr
  | Pi of binder_kind * LeanName.t * expr * expr
  | Proj of LeanName.t * int * expr  (** Proj: name of ind, field, term *)
  | Nat of string
      (** A natural number literal, as the canonical decimal string of its value: each parser validates the
          literal as a Zarith number and keeps [Z.to_string] of it, so that equal values have equal strings;
          the term builder converts it back with [Z.of_string]. Not a [Z.t]: [Lean Import] stores the
          importer's state, these expressions included, in the .vo ([lean_obj] in lean.ml), and rocqchk's
          reader of a .vo (checker/analyze.ml) reads no OCaml custom block, which a Zarith value of 2^62 or
          more is. Job zchk-c83d7e3a-20261127t101628 ran the cut's rocqchk ([ci/build-9.2-cut.sh --check]) on
          tests/core.vo and tests/lean434_bigint.vo built with a [Z.t] here: "Unhandled code 0018", an assert
          at checker/analyze.ml line 420. Rocq's own number tokens (interp/numTok.mli) are strings too. *)
  | String of string

type def = { name : LeanName.t; ty : expr; body : expr; univs : LeanName.t list; }
type ax = { name : LeanName.t; ty : expr; univs : LeanName.t list }

type ind = {
  name : LeanName.t;
  params : (binder_kind * LeanName.t * expr) list;
  ty : expr;
  ctors : (LeanName.t * expr) list;
  univs : LeanName.t list;
}

type notation_kind = Prefix | Infix | Postfix

type notation = {
  kind : notation_kind;
  head : LeanName.t;
  level : int;
  token : string;
}

type entry = Def of def | Ax of ax | Ind of ind | Quot of LeanName.t

type action = Entry of entry | Nota of notation
