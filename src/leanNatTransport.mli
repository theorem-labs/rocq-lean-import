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

type sprop_value = {
  sprop_value : Constr.t;  (** the SProp pass's value, its SProp arguments transported *)
  sprop_count : int;  (** how many arguments it transports (K of its line) *)
  sprop_lemmas : Names.Id.t list;  (** the lemmas they use, in order (IDS of its line) *)
}

type transported = {
  value : Constr.t;  (** the value to try first: the candidate when [relevant > 0], else the SProp pass's value *)
  count : int;  (** K: how many SProp arguments [value] transports *)
  lemmas : Names.Id.t list;  (** IDS: the SProp pass's lemmas, then those of extra SProp sites (L-ids) *)
  relevant : int;  (** R: how many relevant arguments [value] casts; 0 when [value] is the SProp pass's *)
  relevant_lemmas : Names.Id.t list;  (** RIDS: every other lemma [value] uses, first use first, each once *)
  saved : sprop_value option;
      (** when [relevant > 0]: the SProp pass's value, tried if the kernel refuses [value]; [None] when that
          pass changed nothing (then Lean's value is tried) *)
}

val declare_positive_int_option : key:string list -> unit:string -> int option ref -> unit
(** [declare_positive_int_option ~key ~unit r]: the integer option [key] held in [r] ([None] when unset), which
    refuses 0 and the negative values with "<key> must be a positive number of <unit>, not N.". *)

val max_nat_int : Z.t
(** The smallest literal the importer writes in binary form ([large_literal]); below it, [Nat_succ] applied to
    [Nat_zero] as many times as its value. *)

val large_literal : Names.inductive -> Constr.t -> Z.t -> Constr.t
(** [large_literal nat double v], [v] at least [max_nat_int]: [Nat_succ] applied [r] times (1 to 8) to the
    binary form of [v - r] built with [double] ([Nat_double]), [v - r] congruent to 4 modulo 8, so that the
    predecessor of a literal is the literal of its predecessor within each block of 8 (see its comment). The
    transport pass writes the literals it computes in this form too. *)

val transport : context -> Environ.env -> entry:Names.Id.t -> Constr.types -> Constr.t -> transported option
(** [transport ctx env ~entry ty value]: the value [value], of declared type [ty] in [env], of the entry
    whose Rocq name is [entry], with each argument of an application (and the value itself) whose type is an
    SProp type that differs from the expected one only at closed Nat terms of equal value, at closed terms
    that reduce to the same [Fin] of equal values (the Fin case), or at closed terms of a data type with
    different heads that its bounded evaluation proves equal (literal arithmetic, when the lemmas of src/Lean.v
    it needs are registered), under the conditions of README, "Transport of proof arguments across Nat
    literals", cast along the lemmas [<entry>__nat_eq_<k>]; [None] when it changes nothing. A relevant argument
    is cast, along a lemma [<entry>__rel_eq_<k>] and [rel_transport], only in the value of an entry whose type is
    a proposition, only where its declared domain is an inductive type or one applied, and only at Fin places of
    closed values (README, "Transport of proof arguments across Nat literals", the item on relevant positions);
    this is done by a second pass, only after a detector found an argument that passes the gate of that path
    and only when the SProp pass neither stopped nor failed; such an argument is no promise of a cast (the
    second pass may get no lemma for it, stop or fail). Every other non-SProp argument stays as it is. Every step
    of the pass, its type reads, substitutions, comparisons and memo lookups included, is charged before it runs
    (LeanChargedTerm) to the step budget of a part of the entry and to ten times that budget (at most [max_int])
    for all its parts, separately for the SProp pass, the detector and the relevant pass, and, inside one pair of
    literal arithmetic, to the pair's cap; but for the lists of [consts]: their length is known only once [consts]
    returns, and each is charged by its length then ([consts] is asked, once per entry and on each one's own
    budget, for 47 fixed names by the SProp pass and by the relevant pass when it runs, and 56 when literal
    arithmetic is on, and for the 47 only by the detector). It
    calls no unbounded reduction or retyping of Rocq, and an argument whose type it cannot read by its own bounded
    head reduction gets no cast. It logs a generated lemma the kernel refuses (its terms only up to
    [LeanChargedTerm.print_bound] nodes), which leaves the whole argument as it is, and the reason when it stops (a
    budget) or fails (a fixed text); the value is then left as it is. The lemmas it declares stay declared
    whatever becomes of the value. A stop or failure of the detector is not logged and leaves the SProp pass's
    result; a stop or failure of the relevant pass, or its value missing a cast place of the SProp pass, is logged
    ([the relevant pass stops: ...], [the relevant pass fails (E); ...], [the relevant pass keeps J of ...]) and
    leaves the SProp pass's result. *)
