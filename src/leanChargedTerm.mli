(** The charged term layer of the transport pass ({!LeanNatTransport}): a budget of steps, and the term operations
    the pass runs, each charged to that budget before the step or allocation it pays for. It asks Rocq for no
    unbounded reduction or retyping: types are read from declarations, and products and sorts exposed by its own
    head reduction ([whd]). Its memos are fixed-slot physical memos, whose read and write each cost a step, and
    chained tables, which never evict. *)

exception Out_of_budget
(** The current part needs more than its budget, a nesting deeper than [max_depth], or a size estimate larger
    than [max_int]. *)

exception Out_of_total
(** All the parts of the entry together need more than their budget. *)

exception Out_of_pair
(** The current pair of literal arithmetic needs more than its cap ([with_pair]); caught by [with_pair] alone. *)

val max_depth : int
(** The deepest nesting the pass follows, counted from the entry's value or type down through the terms its
    scans and walks visit and the Nat terms it computes; deeper, it stops ([Out_of_budget]) before its recursion
    can exhaust the stack. *)

val check_depth : int -> unit

val add_size : int option -> int option -> int option
(** The sum of two nonnegative size estimates; [None] is a size larger than [max_int]. *)

type 'a memo
(** A fixed-slot physical memo: 512 slots, each empty or holding one term with its result, the array allocated
    by the first write. A term goes to a slot chosen by a bounded hash of the term (at most 10 nodes that carry
    a value among at most 100 visited, a constant cost per node but for a name's label, hashed whole), which
    reads no module path and no universe, so that the same export costs the same steps in whatever file imports
    it; a read compares the term held there with [==] only, a write replaces what the slot holds (no probing,
    resizing or structural comparison). A term whose result was replaced is computed again, at its full
    charge. *)

val memo : unit -> 'a memo

type ('k, 'a) table
(** A chained hash table of keys with their hash. It never evicts. Its hash reads the label of a name, which is
    the Lean name, never its module path (the importing file's library), so that the same export costs the
    same steps in whatever file imports it. *)

val constant_table : unit -> (Names.Constant.t, 'a) table
(** Keyed by [Constant.UserOrd]. *)

val canonical_constant_table : unit -> (Names.Constant.t, 'a) table
(** Keyed by [Constant.CanOrd]. *)

val ind_table : unit -> (Names.inductive, 'a) table
(** Keyed by [Ind.UserOrd]. *)

val globref_table : unit -> (Names.GlobRef.t, 'a) table
(** Keyed by [GlobRef.UserOrd]. *)

val id_table : unit -> (Names.Id.t, 'a) table

val constructor_table : unit -> (Names.constructor, 'a) table
(** Keyed by [Construct.UserOrd]. *)

val held_table : unit -> (Names.Constant.t * Z.t * Z.t, 'a) table
(** Keyed by a function ([Constant.CanOrd]) and two values. *)

val value_table : unit -> (Z.t, 'a) table
(** Keyed by a closed Nat value. *)

type t = {
  genv : Environ.env;  (** the environment the pass reads declarations from *)
  mutable steps : int;  (** the steps left to the current part *)
  mutable total : int;  (** the steps left to all the parts of the entry together *)
  mutable pair : int;  (** the steps left to the current pair of literal arithmetic, [max_int] outside one *)
  mutable in_pair : bool;  (** whether a pair runs *)
  sizes : int option memo;  (** [size] *)
  free : int memo;  (** [free] *)
  normal : Constr.t memo;  (** [nf_beta] *)
}

val create : Environ.env -> steps:int -> total:int -> t
(** With no pair running. *)

val tick : t -> int -> unit
(** [tick ch n] charges [n] (nonnegative) steps to the current part, to the total and to the pair's counter,
    before the work they pay for, and tests them in that order: [Out_of_budget], [Out_of_total] or
    [Out_of_pair] when one goes below zero. *)

val pay : t -> int option -> unit
(** Charge a size estimate: one larger than [max_int] raises [Out_of_budget] before the work; one equal to what
    is left is accepted. *)

val with_pair : t -> int -> (unit -> 'a) -> 'a option
(** [with_pair ch cap f]: [f ()], whose charges are at most [cap] when no pair runs ([None] when they would be
    more), its result when one runs (the pair's counter counts them with the running pair's). The counter is
    [max_int] again once [f] returns or raises; any exception but [Out_of_pair] is raised again. *)

type 'a lookup = Hit of 'a | Miss of int  (** [Miss] carries the slot of the term missed *)

val memo_find : t -> 'a memo -> Constr.t -> 'a lookup
(** One step, then the slot's result when it holds that very term, else the slot. *)

val memo_set : t -> 'a memo -> int -> Constr.t -> 'a -> unit
(** [memo_set ch m slot c v]: one step, then the slot [memo_find] gave for [c] holds [c] and [v]. *)

val table_find : t -> ('k, 'a) table -> 'k -> 'a option
(** One step, and one for each key of the bucket it compares. *)

val table_add : t -> ('k, 'a) table -> 'k -> 'a -> unit
(** One step, and, when the table holds twice as many keys as buckets, one for each key it copies into twice
    as many buckets first. *)

val node_steps : Constr.t -> int
(** The steps of one visit of a node: the node and its immediate subterms. *)

val size : t -> int -> Constr.t -> int option
(** [size ch depth c]: the nodes of [c] as a tree (shared subterms counted at each occurrence), each with its
    own universe data (the instance of a constant, inductive type, constructor, match or array, the levels of a
    sort), computed on the shared term, each node visited charged; [None] above [max_int]. *)

val closed : t -> int -> Constr.t -> bool

val equal : t -> int -> Constr.t -> Constr.t -> bool
(** [Constr.equal], each pair of nodes it compares charged as a visit of the first ([node_steps]). *)

val lift_ch : t -> int -> int -> Constr.t -> Constr.t
(** [lift_ch ch depth n c]: [Vars.lift n c], its size paid first unless [c] is closed. *)

val liftn_ch : t -> int -> int -> int -> Constr.t -> Constr.t
(** [liftn_ch ch depth n k c]: [Vars.liftn n k c] (the indices from [k] on lifted by [n]), its size paid first
    unless [c] is closed. *)

val subst_walk : t -> int -> Constr.t array -> int -> int -> Constr.t -> Constr.t
(** [subst_walk ch depth args lo k c]: [c], under [k] binders that take [args.(lo)] to [args.(lo + k - 1)] (the
    last for [Rel 1]), with them substituted. [k] steps first, then each node it reads or copies, and at each
    place after a replacement's first its size (its lift under binders too). *)

val subst1_ch : t -> int -> Constr.t -> Constr.t -> Constr.t
(** [Vars.subst1], charged as [subst_walk]. *)

val subst_closed : t -> int -> Constr.t array -> int -> int -> Constr.t -> Constr.t
(** [subst_closed ch depth args lo k c]: [subst_walk] for closed replacements, with the same steps for [k] and for
    each node it reads or copies, but with no payment for a replacement placed again and none for a lift: the
    replacement is shared, never copied, so that the term it builds may hold far more nodes as a tree than it
    charged. The caller's obligation: every term of [args] is closed. *)

val app_ch : t -> Constr.t -> Constr.t array -> Constr.t
(** [Constr.mkApp], the copy of both argument arrays charged. *)

val sub_ch : t -> 'a array -> int -> int -> 'a array
(** [Array.sub], charged. *)

val smart_map_ch : t -> ('a -> 'a) -> 'a array -> 'a array
(** [CArray.Smart.map], the copy charged when an element changes. *)

val const_decl : t -> Names.Constant.t -> Declarations.constant_body option
(** The declaration of a constant, one step. *)

val def_body : t -> int -> UVars.Instance.t -> Declarations.constant_body -> Constr.t option
(** The value of a transparent constant at a universe instance (at a nonempty one, its size and the instance's length
    paid first): the one reader of constant bodies. *)

val max_head_steps : int
(** The most steps [whd] takes on one term (64). *)

val beta_closed : t -> int -> Constr.t -> Constr.t array -> Constr.t
(** [f] applied to [args]: each leading lambda takes an argument, one step each, the arguments taken substituted by
    [subst_closed], and the rest applied. *)

val whd :
  ?stop:(Constr.t -> bool) -> t -> Environ.env -> int -> int -> Constr.t -> (int * Constr.t * Constr.t array) option
(** [whd ?stop ch env depth n c]: [c] reduced at its head, [n] steps taken before, by unfolding a transparent
    constant, beta, zeta, a cast, a local definition of [env] and the projection of a constructor's field (no
    match or fixpoint), each step and each substitution and copy charged, until [stop] holds of the term (default:
    never): the steps after, and the head and arguments where it stops. [stop] is tested at each step, after its
    step, nesting and count are checked and before it reduces anything, and never on a projection's subject. A
    projection's step is counted before its subject is reduced, one nesting level deeper. [None] at a projection
    of anything but a constructor, or once the term would take more than [max_head_steps] steps (the count
    checked before each step's substitution). *)

val beta : t -> int -> Constr.t -> Constr.t
(** The beta normal form by its syntax (no constant unfolded), each walk and contraction charged, when a charged scan
    finds a redex; else the term itself. *)

val const_type : t -> int -> Names.Constant.t -> UVars.Instance.t -> Constr.types option
(** The declared type of a constant at a universe instance. *)

val ind_type : t -> int -> Names.inductive -> UVars.Instance.t -> Constr.types option
(** The declared type (arity) of an inductive type at a universe instance; [None] for a template one. *)

val ctor_type : t -> int -> Names.constructor -> UVars.Instance.t -> Constr.types option
(** The declared type of a constructor at a universe instance; [None] for a template inductive type. *)

val expose_prod : t -> Environ.env -> int -> Constr.types -> Constr.types option
(** The type reduced at its head ([whd]) to a product; [None] when [whd] does not get there. *)

val expose_sort : t -> Environ.env -> int -> Constr.types -> Sorts.t option
(** The type reduced at its head ([whd]) to a sort; [None] when [whd] does not get there. *)

val type_of : t -> Environ.env -> int -> Constr.t -> Constr.types option
(** The type of a term, as [Retyping.get_type_of] gives it for the terms it reads: a variable's declared type,
    a global's declared type at its universe instance, the type of an application with its arguments
    substituted (a product exposed by [expose_prod] when the type is not one), of a lambda, of a let, of a cast
    and of a projection of a record (its record type exposed by [whd]). [None] for every other term, and when a
    type it needs is not exposed: no type is guessed and Rocq's unrestricted reduction is never called. *)

val type_relevance : t -> Environ.env -> int -> Constr.types -> Sorts.relevance option
(** The relevance of a type: that of its sort, read by [type_of] and [whd]; a product has that of its codomain.
    [None] when it cannot be read. *)

val print_bound : int
(** The most nodes the optional diagnostics of the pass and of its caller print of their terms. *)

val printable : Constr.t list -> bool
(** Whether the terms have at most [print_bound] nodes in all, counted by a walk that stops after that many
    (each shared subterm counted at each occurrence). *)
