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
    SProp type that differs from the expected one only at closed Nat terms of equal value, or at closed terms
    that reduce to the same [Fin] of equal values (the Fin case, under the conditions of README, "Transport of
    proof arguments across Nat literals"), cast along the lemmas [<entry>__nat_eq_<k>]; [None] when it changes
    nothing. The non-SProp arguments stay as they are. Every step of the pass, its type reads, substitutions,
    comparisons and memo lookups included, is charged before it runs (LeanChargedTerm) to the step budget of a
    part of the entry, and to ten times that budget (at most [max_int]) for all its parts, but for the lists of
    [consts]: their length is known only once [consts] returns, and each is charged by its length then
    ([consts] is asked for 19 fixed names, once per entry). It calls no unbounded reduction or retyping of Rocq,
    and an argument whose type it cannot read by its own bounded head reduction gets no cast. It logs a
    generated lemma the kernel refuses (its terms only up to [LeanChargedTerm.print_bound] nodes), and the
    reason when it stops (a budget) or fails (a fixed text); the value is then left as it is. The lemmas it
    declares stay declared whatever becomes of the value. *)
