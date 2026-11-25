(** Transport of SProp arguments across closed Nat terms of equal value (README, "Transport of proof
    arguments across Nat literals").

    Rocq reduces Lean's [Nat.add], [Nat.mul] and [Nat.pow] on the unary [Nat] of src/Lean.v one [Nat_succ]
    at a time, so its kernel cannot convert [n < UInt32.size] with [n < 2 ^ 32] where Lean's kernel computes
    both sides with GMP. [transport] casts such an argument with [sprop_transport] (src/Lean.v) along a
    generated lemma [x = y], which it declares through [declare] and the kernel checks like any constant. *)

type context = {
  consts : string list -> Names.Constant.t list;
      (** The constants of every declared instance of the export's entry of that Lean name, for example
          [["Nat"; "add"]]; none when the export has not declared it. *)
  declare : Names.Id.t -> Constr.types -> Constr.t -> Names.GlobRef.t;
      (** Declare a constant without universes of that name, type and value, with every kernel check. *)
  log : Pp.t -> unit;  (** Print a line of the import's output about the entry. *)
}

type transported = {
  value : Constr.t;  (** the value, its SProp arguments transported *)
  count : int;  (** how many arguments it transports *)
  lemmas : Names.Id.t list;  (** the lemmas they use, in order *)
}

val transport : context -> Environ.env -> entry:Names.Id.t -> Constr.types -> Constr.t -> transported option
(** [transport ctx env ~entry ty value]: the value [value], of declared type [ty] in [env], of the entry
    whose Rocq name is [entry], with each argument of an application (and the value itself) whose type is an
    SProp type that differs from the expected one only at closed Nat terms of equal value cast along the
    lemmas [<entry>__nat_eq_<k>]; [None] when it changes nothing. The non-SProp arguments stay as they are.
    It logs a generated lemma the kernel refuses, and the reason when it stops (a step budget per entry) or
    fails; the value is then left as it is. The lemmas it declares stay declared whatever becomes of the
    value. *)
