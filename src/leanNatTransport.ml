(* Transport of SProp arguments across closed Nat terms of equal value (see the .mli and README, "Transport
   of proof arguments across Nat literals"). The values this module computes with OCaml's Z are not trusted:
   they only find the places to transport. Each place gets a lemma [x = y], and the kernel checks it; a wrong
   value gives a lemma the kernel refuses. For two Nat terms the proof goes through Rocq's binary [N] (the
   lemmas after [toN] in src/Lean.v); for the two values of a [Fin] (the Fin case, [fin_hole]) it is
   [Logic.eq_refl], which the kernel checks on the unary [Nat], so the value and every operand but a divisor
   are below [fin_ceiling].

   The pass is optional work: every step of it is charged to a budget before the step or allocation it pays
   for ([tick], [pay]), and it asks Rocq for no unbounded reduction or retyping. It reads types and exposes
   products and sorts by its own charged head reduction (unfolding of a transparent constant, beta, zeta, cast,
   projection of a constructor, [whd]); a type it cannot read that way is no type, and the argument gets no
   cast. When it stops, Lean's own value goes to the kernel, which checks it as without the pass. *)

open Names

type context = {
  consts : string list -> Constant.t list;
  declare : Id.t -> Constr.types -> Constr.t -> GlobRef.t;
  log : Pp.t -> unit;
}

type transported = { value : Constr.t; count : int; lemmas : Id.t list }

(* The smallest value worth a lemma: the kernel compares smaller ones unit by unit quickly enough. *)
let transport_min = Z.of_int 4096

(* The Fin case covers Fin values below this one: its lemma is [eq_refl], which the kernel checks by computing
   [t % 2 ^ 32] on the unary [Nat], in time and stack that grow with [t]. *)
let fin_ceiling = Z.of_int 65536

(* The largest value, in bits, the finder computes: a certificate checks binary arithmetic on it. *)
let max_bits = 1024

(* A certificate of a literal below this value is [Logic.eq_refl]: the kernel computes [toN] of it. *)
let small_literal = Z.of_int 8192

(* The budget charges the work of one part of an entry: the entry's own scans and walks are one part, and each
   argument the pass looks at is another. A reused certificate costs its full number of steps again: the kernel
   checks the expanded proof tree. All the parts of one entry together get [total_factor] times the budget.
   [Set Lean Transport Step Budget N.] sets it (README, "Lean Transport Step Budget"). *)
let default_budget = 1_000_000

let total_factor = 10

let budget_option = ref None

let () =
  Goptions.declare_int_option
    {
      optdepr = None;
      optstage = Interp;
      optkey = [ "Lean"; "Transport"; "Step"; "Budget" ];
      optread = (fun () -> !budget_option);
      optwrite =
        (fun x ->
          (match x with
          | Some n when n <= 0 ->
            CErrors.user_err
              Pp.(str "Lean Transport Step Budget must be a positive number of steps, not " ++ int n ++ str ".")
          | None | Some _ -> ());
          budget_option := x);
    }

let budget () = Option.default default_budget !budget_option

(* The steps of all the parts of one entry together. *)
let total_budget () =
  let n = budget () in
  if n > max_int / total_factor then max_int else total_factor * n

(* The deepest nesting the pass follows: the Nat terms the finder computes, and the terms its scans and walks
   go through, counted together from the entry's value or type down. Deeper, the pass stops ([Out_of_budget])
   before its recursion can exhaust the stack. *)
let max_depth = 10_000

exception Out_of_budget

(* All the parts of one entry together need more than [total_budget ()] steps. *)
exception Out_of_total

let check_depth depth = if depth > max_depth then raise Out_of_budget

(* What the pass uses from src/Lean.v and Corelib. *)
type refs = {
  nt_nat : inductive;
  nt_double : Constant.t;
  nt_eq : inductive;
  nt_fin : inductive;  (** src/Lean.v's [Fin], the type Lean's [Fin] is predeclared to *)
  nt_n : Constr.t;
  nt_n0 : Constr.t;
  nt_npos : Constr.t;
  nt_xh : Constr.t;
  nt_xo : Constr.t;
  nt_xi : Constr.t;
  nt_refl : Constr.t;
  nt_succ_step : Constr.t;
  nt_double_step : Constr.t;
  nt_unfold_step : Constr.t;
  nt_op_step : Constr.t;
  nt_nat_eq : Constr.t;
  nt_transport : Constr.t;
}

let lib_ref s = match Rocqlib.lib_ref_opt s with Some r -> r | None -> raise Not_found
let lib_term s = Constr.mkRef (lib_ref s, UVars.Instance.empty)

(* [None] when one of them is not registered (a src/Lean.v without the transport lemmas). *)
let refs () =
  try
    match (lib_ref "lean.Nat", lib_ref "lean.Nat_double", lib_ref "lean.Eq", lib_ref "lean.Fin") with
    | GlobRef.IndRef nt_nat, GlobRef.ConstRef nt_double, GlobRef.IndRef nt_eq, GlobRef.IndRef nt_fin ->
      Some
        {
          nt_nat;
          nt_double;
          nt_eq;
          nt_fin;
          nt_n = lib_term "num.N.type";
          nt_n0 = lib_term "num.N.N0";
          nt_npos = lib_term "num.N.Npos";
          nt_xh = lib_term "num.pos.xH";
          nt_xo = lib_term "num.pos.xO";
          nt_xi = lib_term "num.pos.xI";
          nt_refl = lib_term "core.eq.refl";
          nt_succ_step = lib_term "lean.toN_succ_step";
          nt_double_step = lib_term "lean.toN_double_step";
          nt_unfold_step = lib_term "lean.toN_unfold_step";
          nt_op_step = lib_term "lean.toN_op_step";
          nt_nat_eq = lib_term "lean.Nat_eq_of_toN";
          nt_transport = lib_term "lean.sprop_transport";
        }
    | _ -> None
  with Not_found -> None

let nat_type nt = Constr.mkIndU (nt.nt_nat, UVars.Instance.empty)
let nat_zero nt = Constr.mkConstructU ((nt.nt_nat, 1), UVars.Instance.empty)
let nat_succ nt t = Constr.mkApp (Constr.mkConstructU ((nt.nt_nat, 2), UVars.Instance.empty), [| t |])
let refl_nat nt t = Constr.mkApp (nt.nt_refl, [| nat_type nt; t |])
let refl_n nt w = Constr.mkApp (nt.nt_refl, [| nt.nt_n; w |])
let lam1 nt body = Constr.mkLambda (Context.nameR (Id.of_string "n"), nat_type nt, body)

let lam2 nt body =
  Constr.mkLambda
    ( Context.nameR (Id.of_string "a"),
      nat_type nt,
      Constr.mkLambda (Context.nameR (Id.of_string "b"), nat_type nt, body) )

(* The binary literal of [v] (Rocq's [N]), at most [max_bits] bits long. *)
let n_literal nt v =
  let rec pos v =
    if Z.equal v Z.one then nt.nt_xh
    else Constr.mkApp ((if Z.testbit v 0 then nt.nt_xi else nt.nt_xo), [| pos (Z.shift_right v 1) |])
  in
  if Z.equal v Z.zero then nt.nt_n0 else Constr.mkApp (nt.nt_npos, [| pos v |])

let bounded v = if Z.numbits v <= max_bits then Some v else None

let z_pow b e =
  if Z.gt e (Z.of_int max_bits) then None
  else if Z.leq b Z.one then Some (if Z.equal e Z.zero then Z.one else b)
  else if Z.numbits b * Z.to_int e > 2 * max_bits then None
  else bounded (Z.pow b (Z.to_int e))

(* The shape of a term, the constants named by their Lean names: Lean's [Nat], any term, or one of the
   constants applied to arguments of those shapes. *)
type 'k pat = Nat_type | Any | Inst of 'k * 'k pat list

type nat_op = Add | Mul | Pow

(* One row per operation: the export's function and class function, the Nat instance of the class function
   as Lean's prelude builds it, the value, Rocq's [N] function and the [toN] lemma of src/Lean.v with its
   arguments after the export's function [g]: the lemma of the operation it is defined from ([prev]) and its
   defining equations, each closed by [Logic.eq_refl] on open terms (as Lean's [Nat.pow_succ := rfl]). *)
type op_spec = {
  op : nat_op;
  fun_name : string list;
  class_name : string list;
  inst : string list pat;
  z : Z.t -> Z.t -> Z.t option;
  n_fun : string;
  to_n_lemma : string;
  prev : nat_op option;
  lemma_args : refs -> prev:(Constr.t * Constr.t) option -> Constr.t -> Constr.t array option;
}

let r1 = Constr.mkRel 1
let r2 = Constr.mkRel 2
let app f a = Constr.mkApp (f, a)

let op_specs =
  [
    {
      op = Add;
      fun_name = [ "Nat"; "add" ];
      class_name = [ "HAdd"; "hAdd" ];
      inst = Inst ([ "instHAdd" ], [ Nat_type; Inst ([ "instAddNat" ], []) ]);
      z = (fun a b -> bounded (Z.add a b));
      n_fun = "lean.N.add";
      to_n_lemma = "lean.toN_add";
      prev = None;
      lemma_args =
        (fun nt ~prev:_ add ->
          (* add n 0 = n, add n (S m) = S (add n m) *)
          Some [| add; lam1 nt (refl_nat nt r1); lam2 nt (refl_nat nt (nat_succ nt (app add [| r2; r1 |]))) |]);
    };
    {
      op = Mul;
      fun_name = [ "Nat"; "mul" ];
      class_name = [ "HMul"; "hMul" ];
      inst = Inst ([ "instHMul" ], [ Nat_type; Inst ([ "instMulNat" ], []) ]);
      z = (fun a b -> bounded (Z.mul a b));
      n_fun = "lean.N.mul";
      to_n_lemma = "lean.toN_mul";
      prev = Some Add;
      lemma_args =
        (fun nt ~prev mul ->
          (* mul n 0 = 0, mul n (S m) = add (mul n m) n *)
          Option.map
            (fun (add, hadd) ->
              [| add; mul; hadd; lam1 nt (refl_nat nt (nat_zero nt));
                 lam2 nt (refl_nat nt (app add [| app mul [| r2; r1 |]; r2 |])) |])
            prev);
    };
    {
      op = Pow;
      fun_name = [ "Nat"; "pow" ];
      class_name = [ "HPow"; "hPow" ];
      inst =
        Inst
          ( [ "instHPow" ],
            [ Nat_type; Nat_type; Inst ([ "instPowNat" ], [ Nat_type; Inst ([ "instNatPowNat" ], []) ]) ] );
      z = z_pow;
      n_fun = "lean.N.pow";
      to_n_lemma = "lean.toN_pow";
      prev = Some Mul;
      lemma_args =
        (fun nt ~prev pow ->
          (* pow b 0 = 1, pow b (S e) = mul (pow b e) b *)
          Option.map
            (fun (mul, hmul) ->
              [| mul; pow; hmul; lam1 nt (refl_nat nt (nat_succ nt (nat_zero nt)));
                 lam2 nt (refl_nat nt (app mul [| app pow [| r2; r1 |]; r2 |])) |])
            prev);
    };
  ]

(* A row at one entry: its constants in the export. *)
type op_row = {
  spec : op_spec;
  funs : Constant.t list;
  classes : Constant.t list;
  inst_pat : Constant.t list pat;
}

(* The forms of a closed Nat term: a literal of the importer's form ([Zero], [Succ], [Double], see
   [nat_int] in lean.ml), a term that unfolds to another ([Unfold]: a constant of type Nat, or
   [OfNat.ofNat Nat n (instOfNatNat m)] to [m]), and an operation of a row as the term applies it
   ([Op (row, f, a, b)]: [f a b], [f] the export's function or the class function at its Nat instance). *)
type nat_form =
  | Zero
  | Succ of Constr.t
  | Double of Constr.t
  | Unfold of Constr.t
  | Op of op_row * Constr.t * Constr.t * Constr.t

(* Size estimates of terms not yet paid for: [None] is a size larger than [max_int] (an estimate that cannot
   be represented, which is never [max_int] itself). Both operands are nonnegative. *)
let add_size a b = match (a, b) with Some a, Some b when a <= max_int - b -> Some (a + b) | _ -> None

(* The memo of one kind of result, keyed by a term itself: [memo_slots] slots, each empty or holding one term
   with its result, the array allocated by the first write. A term goes to the slot
   [Hashtbl.hash_param 10 100 term land (memo_slots - 1)]: a read compares the term in that slot with [==] only,
   a write replaces what the slot holds. There is no probing, resizing or structural comparison, so a read or a
   write costs at most one comparison, whatever the terms that share a slot (a unary literal puts every suffix
   of its successor chain in the same slot); a term whose result was replaced is computed again, at its full
   charge. The bounds 10 and 100 are those of [Hashtbl.hash] in the OCaml of the Rocq 9.2 cut, here explicit:
   on the cut's switch, [ocamlfind ocamlopt -version] prints 4.14.2 and its stdlib's hashtbl.ml reads
   [let hash x = seeded_hash_param 10 100 0 x] (BET-1525 Job r8cand-20261125t231714, ocaml-version.txt). *)
let memo_slots = 512

type 'a memo = { mutable slots : (Constr.t * 'a) option array }

let memo () = { slots = [||] }
let memo_slot c = Hashtbl.hash_param 10 100 c land (memo_slots - 1)

(* The steps charged for one lookup or one addition in a balanced map of [n] entries ([Indmap_env],
   [Id.Set], AVL trees): it visits at most 1.44 * log2 (n + 2) nodes, which [3 * numbits (n + 1) + 2]
   bounds. *)
let map_steps n =
  let rec bits n k = if n = 0 then k else bits (n lsr 1) (k + 1) in
  (3 * bits (n + 1) 0) + 2

(* A hash table of the pass: an array of buckets, each a list of keys with their values. A lookup pays one
   step and one more for each entry of its bucket it compares; an addition pays one step, and, when the table
   holds twice as many entries as buckets, the copy of every entry into twice as many buckets first. Keys are
   hashed by Rocq's cached name hashes. *)
type ('k, 'a) table = {
  hash : 'k -> int;
  eq : 'k -> 'k -> bool;
  mutable buckets : ('k * 'a) list array;
  mutable entries : int;
}

let table hash eq = { hash; eq; buckets = Array.make 16 []; entries = 0 }

(* The constant maps of the memos (by user name, as Rocq's [Cmap_env]). *)
type 'a cmap = (Constant.t, 'a) table

let cmap () = table Constant.UserOrd.hash Constant.UserOrd.equal

type state = {
  ctx : context;
  refs : refs;
  genv : Environ.env;
  mutable rows : op_row list;
  mutable of_nat : Constant.t list;
  mutable inst_of_nat : Constant.t list;
  mutable triggers : (Constant.t, unit) table;  (** the constants that may make an entry need the pass *)
  mutable mods : Constant.t list;  (** the export's [Nat.mod] *)
  mutable hmods : Constant.t list;  (** the export's [HMod.hMod] *)
  mutable hmod_nat : Constant.t list pat;  (** Nat's instance of [HMod.hMod] *)
  mutable lemma_ops : (nat_op * (Constr.t * Constr.t) option) list;  (** [lemma_of], at most one per row *)
  mutable unary_succ : bool;  (** [Nat_succ]'s declared type is one relevant Nat argument to Nat *)
  mutable unary_double : bool;  (** the same for [Nat_double] *)
  mutable records : bool Indmap_env.t;  (** [one_field_record], per inductive type *)
  mutable n_records : int;
  fin_consts : bool cmap;  (** [fin_typed_const], per constant *)
  entry : Id.t;
  mutable steps : int;
  mutable total : int;  (** the steps left to all the parts of the entry together *)
  values : Z.t option memo;
  const_values : Z.t option cmap;
  fin_values : Z.t option memo;  (** [fin_value], per term *)
  const_fin_values : Z.t option cmap;  (** [fin_value], per constant *)
  certs : (Z.t * Constr.t * int) option memo;
  const_certs : (Z.t * Constr.t * int) option cmap;
  sizes : int option memo;  (** [size] *)
  free : int memo;  (** [free] *)
  normal : Constr.t memo;  (** [nf_beta] *)
  mutable next : int;  (** the number of the next lemma this entry generates *)
  mutable count : int;  (** arguments transported *)
  mutable lemmas : Id.t list;  (** the lemmas they use, last first *)
  mutable lemma_ids : Id.Set.t;  (** the same, as a set *)
  mutable n_lemma_ids : int;
}

(* Charge [n] steps (nonnegative) to the current part and to the entry's total, before the work they pay for.
   Both are at most [max_int] and nonnegative before, so neither subtraction can overflow. *)
let tick st n =
  st.steps <- st.steps - n;
  st.total <- st.total - n;
  if st.steps < 0 then raise Out_of_budget;
  if st.total < 0 then raise Out_of_total

(* Charge a size estimate: an estimate larger than [max_int] stops the pass before the work, as a part's own
   budget does; an estimate equal to what is left is accepted. *)
let pay st = function None -> raise Out_of_budget | Some n -> tick st n

let memo_get st m c =
  tick st 1;
  if Array.length m.slots = 0 then None
  else match m.slots.(memo_slot c) with Some (k, v) when k == c -> Some v | Some _ | None -> None

let memo_put st m c v =
  tick st 1;
  if Array.length m.slots = 0 then m.slots <- Array.make memo_slots None;
  m.slots.(memo_slot c) <- Some (c, v)

let table_find st t k =
  tick st 1;
  let rec look = function
    | [] -> None
    | (k', v) :: rest ->
      tick st 1;
      if t.eq k k' then Some v else look rest
  in
  look t.buckets.(t.hash k land (Array.length t.buckets - 1))

let table_add st t k v =
  let n = Array.length t.buckets in
  if t.entries >= 2 * n then begin
    tick st (t.entries + (2 * n));
    let wide = Array.make (2 * n) [] in
    Array.iter
      (List.iter (fun ((k, _) as e) ->
           let i = t.hash k land ((2 * n) - 1) in
           wide.(i) <- e :: wide.(i)))
      t.buckets;
    t.buckets <- wide
  end;
  tick st 1;
  let i = t.hash k land (Array.length t.buckets - 1) in
  t.buckets.(i) <- (k, v) :: t.buckets.(i);
  t.entries <- t.entries + 1

(* The steps of one visit of [c]: the node and its immediate subterms, which bounds what the visit reads and
   what a copy of the node allocates. *)
let node_steps c =
  match Constr.kind c with
  | Constr.App (_, a) -> 2 + Array.length a
  | Constr.Case (_, _, pms, _, _, _, bl) -> 4 + Array.length pms + Array.length bl
  | Constr.Fix (_, (_, tl, _)) | Constr.CoFix (_, (_, tl, _)) -> 1 + (2 * Array.length tl)
  | Constr.Array (_, t, _, _) -> 3 + Array.length t
  | Constr.Prod _ | Constr.Lambda _ | Constr.Cast _ -> 3
  | Constr.LetIn _ -> 4
  | Constr.Proj _ -> 2
  | Constr.Rel _ | Constr.Var _ | Constr.Meta _ | Constr.Evar _ | Constr.Sort _ | Constr.Const _ | Constr.Ind _
  | Constr.Construct _ | Constr.Int _ | Constr.Float _ | Constr.String _ ->
    1

let is_leaf c =
  match Constr.kind c with
  | Constr.Rel _ | Constr.Var _ | Constr.Meta _ | Constr.Sort _ | Constr.Const _ | Constr.Ind _ | Constr.Construct _
  | Constr.Int _ | Constr.Float _ | Constr.String _ ->
    true
  | _ -> false

(* A leaf without a de Bruijn index: a constant, constructor, inductive type, sort, variable or literal. *)
let closed_leaf c =
  match Constr.kind c with
  | Constr.Var _ | Constr.Meta _ | Constr.Sort _ | Constr.Const _ | Constr.Ind _ | Constr.Construct _ | Constr.Int _
  | Constr.Float _ | Constr.String _ ->
    true
  | _ -> false

(* The term under a run of applications of closed leaves to one argument each ([Nat_succ (Nat_succ ...)], a
   unary literal of the importer), and the length [j] of the run: one step for each application, which the
   loop reads and follows, so that a reader of the memos below looks up only the run's top. *)
let rec unary_run st c j =
  match Constr.kind c with
  | Constr.App (h, [| x |]) when closed_leaf h ->
    tick st 1;
    unary_run st x (j + 1)
  | _ -> (c, j)

(* The number of nodes of [c] as a tree, its shared subterms counted at each occurrence, computed on the shared
   term: what a walk of [c] by Rocq ([Vars.lift], [Vars.substl], [Vars.subst_instance_constr]) visits. *)
let rec size st depth c =
  if is_leaf c then Some 1
  else
    match memo_get st st.sizes c with
    | Some s -> s
    | None ->
      check_depth depth;
      let s =
        match unary_run st c 0 with
        | b, j when j > 0 ->
          (* each application of the run and its head: [2 * j] nodes, fewer than the nodes in memory *)
          add_size (Some (2 * j)) (size st (depth + 1) b)
        | _ ->
          tick st (node_steps c);
          Constr.fold
            (fun acc c -> match acc with None -> None | Some _ -> add_size acc (size st (depth + 1) c))
            (Some 1) c
      in
      memo_put st st.sizes c s;
      s

(* The greatest de Bruijn index free in [c] (0 when [c] is closed), of [c] itself: a visit under [k] binders
   reads it against [k]. *)
let rec free st depth c =
  match Constr.kind c with
  | Constr.Rel i -> i
  | Constr.Var _ | Constr.Meta _ | Constr.Sort _ | Constr.Const _ | Constr.Ind _ | Constr.Construct _ | Constr.Int _
  | Constr.Float _ | Constr.String _ ->
    0
  | _ -> (
    match memo_get st st.free c with
    | Some f -> f
    | None ->
      check_depth depth;
      let f =
        match unary_run st c 0 with
        | b, j when j > 0 -> free st (depth + 1) b
        | _ ->
          tick st (node_steps c);
          Constr.fold_constr_with_binders succ (fun k acc c -> max acc (free st (depth + 1) c - k)) 0 0 c
      in
      memo_put st st.free c f;
      f)

let closed st depth c = free st depth c = 0

(* [Constr.equal], each pair of nodes it compares charged; physically equal terms are equal at once. *)
let rec equal st depth a b =
  a == b
  ||
  (tick st 1;
   check_depth depth;
   Constr.compare_head_gen
     (fun _ u u' -> UVars.Instance.equal u u')
     Sorts.equal
     (fun (e, l) (e', l') -> Evar.equal e e' && SList.equal (equal st (depth + 1)) l l')
     (fun _ a b -> equal st (depth + 1) a b)
     0 a b)

(* [Vars.lift n c], paid before: Rocq's lift walks and may copy the whole tree of [c] (theorem-labs/rocq at
   07e45e36, kernel/constr.ml [exliftn]: [map_with_binders]), which a closed [c] does not need. *)
let lift_ch st depth n c =
  if n = 0 || closed st depth c then c
  else begin
    pay st (size st depth c);
    Vars.lift n c
  end

(* [Vars.substl] of the array [lamv] ([lamv.(0)] for [Rel 1]) in [c], each node charged before it is read or
   copied. It goes only into the subterms with a free index its substitution changes. A replacement substituted
   at more than one place duplicates itself: each place after its first pays the size of the replacement as a
   tree, the work a later walk of the result will do there, so a substitution that would build a term of more
   than [max_int] nodes stops before it is made; and a replacement under binders pays its lift. *)
let subst_walk st depth lamv c =
  let lv = Array.length lamv in
  let placed = Array.make lv false in
  let rec go depth k c =
    if free st depth c <= k then c
    else begin
      tick st (node_steps c);
      check_depth depth;
      match Constr.kind c with
      | Constr.Rel i -> if i - k <= lv then place depth k (i - k - 1) else Constr.mkRel (i - lv)
      | _ -> Constr.map_with_binders succ (go (depth + 1)) k c
    end
  and place depth k j =
    let v = lamv.(j) in
    if placed.(j) then pay st (size st depth v) else placed.(j) <- true;
    lift_ch st depth k v
  in
  go depth 0 c

(* [Vars.subst1 v c], charged. *)
let subst1_ch st depth v c =
  tick st 1;
  subst_walk st depth [| v |] c

(* [Vars.substl l c], the list copied into an array after its charge. *)
let substl_ch st depth l c =
  match l with
  | [] -> c
  | _ :: _ ->
    tick st (List.length l);
    subst_walk st depth (Array.of_list l) c

(* [c], under [k] binders that take [args.(0)] to [args.(k - 1)] (the last for [Rel 1]), with them substituted. *)
let subst_args st depth c args k =
  if k = 0 then c
  else begin
    tick st k;
    subst_walk st depth (Array.init k (fun i -> args.(k - 1 - i))) c
  end

(* [Constr.mkApp (f, args)]: a copy of both argument arrays when [f] is itself an application. *)
let app_ch st f args =
  if Array.length args = 0 then f
  else begin
    tick st (Array.length args + (match Constr.kind f with Constr.App (_, a) -> Array.length a | _ -> 0));
    Constr.mkApp (f, args)
  end

(* [Array.sub a i n], charged. *)
let sub_ch st a i n =
  tick st n;
  Array.sub a i n

(* [CArray.Smart.map f a], the copy of [a] charged when an element changes. *)
let smart_map_ch st f a =
  let n = Array.length a in
  let rec go i =
    if i = n then a
    else
      let x' = f a.(i) in
      if x' == a.(i) then go (i + 1)
      else begin
        tick st n;
        let a' = Array.copy a in
        a'.(i) <- x';
        for j = i + 1 to n - 1 do
          a'.(j) <- f a.(j)
        done;
        a'
      end
  in
  go 0

let mem_const st c l =
  List.exists
    (fun c' ->
      tick st 1;
      Constant.CanOrd.equal c c')
    l

let is_nat_ind st c =
  match Constr.kind c with Constr.Ind (ind, _) -> Ind.CanOrd.equal ind st.refs.nt_nat | _ -> false

(* The patterns are the fixed rows above; a list of constants they name is the export's and is charged in
   [mem_const]. *)
let rec pat_matches st p c =
  match p with
  | Nat_type -> is_nat_ind st c
  | Any -> true
  | Inst (ks, ps) -> (
    let h, args = Constr.decompose_app c in
    let rec all i = function [] -> true | p :: ps -> pat_matches st p args.(i) && all (i + 1) ps in
    match Constr.kind h with
    | Constr.Const (k, _) -> Array.length args = List.length ps && mem_const st k ks && all 0 ps
    | _ -> false)

(* [c] at the universe instance [u]: for a nonempty [u] Rocq's [Vars.subst_instance_constr] walks and copies
   the whole tree of [c] (theorem-labs/rocq at 07e45e36, kernel/vars.ml), so its size and [u] are paid first;
   at the empty instance [c] is used as it is. *)
let instantiate st depth u c =
  if UVars.Instance.is_empty u then c
  else begin
    let q, l = UVars.Instance.length u in
    pay st (add_size (size st depth c) (Some (q + l)));
    Vars.subst_instance_constr u c
  end

(* The value of the constant [cu] when it is transparent (and of type Nat when [nat]), at its universe
   instance: the one reader of constant bodies. *)
let const_body st depth ~nat (k, u) =
  tick st 1;
  match Environ.lookup_constant_opt k st.genv with
  | Some cb when (not nat) || is_nat_ind st cb.Declarations.const_type -> (
    match cb.Declarations.const_body with Declarations.Def b -> Some (instantiate st depth u b) | _ -> None)
  | Some _ | None -> None

(* The one recognizer of the Nat forms: every guard is here. *)
let nat_form st depth c =
  let h, args = Constr.decompose_app c in
  let nargs = Array.length args in
  match Constr.kind h with
  | Constr.Construct ((ind, 1), _) when nargs = 0 && Ind.CanOrd.equal ind st.refs.nt_nat -> Some Zero
  | Constr.Construct ((ind, 2), _) when nargs = 1 && Ind.CanOrd.equal ind st.refs.nt_nat -> Some (Succ args.(0))
  | Constr.Const (k, _) when nargs = 1 && Constant.CanOrd.equal k st.refs.nt_double -> Some (Double args.(0))
  | Constr.Const cu when nargs = 0 -> Option.map (fun b -> Unfold b) (const_body st depth ~nat:true cu)
  | Constr.Const (k, _)
    when nargs = 3 && mem_const st k st.of_nat && is_nat_ind st args.(0)
         && pat_matches st (Inst (st.inst_of_nat, [ Any ])) args.(2) ->
    Some (Unfold (snd (Constr.decompose_app args.(2))).(0))
  | Constr.Const (k, _) when nargs = 6 ->
    List.find_map
      (fun row ->
        if mem_const st k row.classes && is_nat_ind st args.(0) && is_nat_ind st args.(1)
           && is_nat_ind st args.(2) && pat_matches st row.inst_pat args.(3)
        then Some (Op (row, Constr.mkApp (h, Array.sub args 0 4), args.(4), args.(5)))
        else None)
      st.rows
  | Constr.Const (k, _) when nargs = 2 ->
    List.find_map (fun row -> if mem_const st k row.funs then Some (Op (row, h, args.(0), args.(1))) else None) st.rows
  | _ -> None

(* The memo of [c]: its constant's when it is a constant without universe instance, else its own. *)
let memo_find st phys consts c =
  match Constr.kind c with
  | Constr.Const (k, u) when UVars.Instance.is_empty u -> table_find st consts k
  | _ -> memo_get st phys c

let memo_add st phys consts c v =
  match Constr.kind c with
  | Constr.Const (k, u) when UVars.Instance.is_empty u -> table_add st consts k v
  | _ -> memo_put st phys c v

(* The term under a run of [Nat_succ] applications, and [j] plus the length of the run: one step each, as
   [compute] charges a node, in a loop. *)
let rec succ_run st c j =
  match Constr.kind c with
  | Constr.App (h, [| x |])
    when (match Constr.kind h with
         | Constr.Construct ((ind, 2), _) -> Ind.CanOrd.equal ind st.refs.nt_nat
         | _ -> false) ->
    tick st 1;
    succ_run st x (j + 1)
  | _ -> (c, j)

(* The value of the closed Nat term [c]; each term (or constant) is computed again only when its slot of the
   memo holds another term. *)
let rec value st depth c =
  match memo_find st st.values st.const_values c with
  | Some v -> v
  | None ->
    let v = compute st depth c in
    memo_add st st.values st.const_values c v;
    v

and compute st depth c =
  tick st 1;
  check_depth depth;
  match nat_form st depth c with
  | None -> None
  | Some f ->
    let value = value st (depth + 1) in
    (match f with
    | Zero -> Some Z.zero
    | Succ m ->
      (* [c] is [Nat_succ] applied [j] times to [b]; its value is the largest of the run, the one bounded *)
      let b, j = succ_run st m 1 in
      Option.bind (value b) (fun v -> bounded (Z.add v (Z.of_int j)))
    | Double m -> Option.bind (value m) (fun v -> bounded (Z.shift_left v 1))
    | Unfold b -> value b
    | Op (row, _, a, b) -> (match (value a, value b) with Some x, Some y -> row.spec.z x y | _ -> None))

(* Whether [c] is a literal of the importer's form. *)
let rec is_literal st depth c =
  check_depth depth;
  match nat_form st depth c with
  | Some Zero -> true
  | Some (Succ m | Double m) ->
    tick st 1;
    is_literal st (depth + 1) m
  | Some (Unfold _ | Op _) | None -> false

(* The literal [c] unfolds to, if it is one: the kernel converts two terms of the same literal without
   arithmetic. *)
let rec literal_of st depth c =
  check_depth depth;
  if is_literal st depth c then Some c
  else
    match nat_form st depth c with
    | Some (Unfold b) ->
      tick st 1;
      literal_of st (depth + 1) b
    | Some (Zero | Succ _ | Double _ | Op _) | None -> None

(* The export's function of [op] without universes, as a term, and its [toN] lemma. *)
let rec lemma_of st op =
  match List.assoc_opt op st.lemma_ops with
  | Some l -> l
  | None ->
    let row = List.find (fun row -> row.spec.op = op) st.rows in
    let g =
      List.find_map
        (fun c ->
          tick st 1;
          if UVars.AbstractContext.is_empty (Declareops.constant_polymorphic_context (Environ.lookup_constant c st.genv))
          then Some (Constr.mkConstU (c, UVars.Instance.empty))
          else None)
        row.funs
    in
    let l =
      Option.bind g (fun g ->
          let prev = Option.bind row.spec.prev (lemma_of st) in
          Option.map (fun args -> (g, app (lib_term row.spec.to_n_lemma) args)) (row.spec.lemma_args st.refs ~prev g))
    in
    st.lemma_ops <- (op, l) :: st.lemma_ops;
    l

(* The value [v] of [t], a proof of [Logic.eq (toN t) w] for [w] the binary literal of [v], and the size of
   that proof; [None] when [t] has no value or an operation it needs has no [toN] lemma. Every step states
   its own term, so that the kernel only compares a term with itself, and checks each binary operation on
   literals. A proof built once is used again, its size counted again. *)
let rec certify st depth t =
  match memo_find st st.certs st.const_certs t with
  | Some r ->
    Option.iter (fun (_, _, size) -> tick st size) r;
    r
  | None ->
    let r = certify_node st depth t in
    memo_add st st.certs st.const_certs t r;
    r

and certify_node st depth t =
  check_depth depth;
  let nt = st.refs in
  match value st depth t with
  | None -> None
  | Some v ->
    tick st 1;
    let w = n_literal nt v in
    if Z.lt v small_literal && is_literal st depth t then Some (v, refl_n nt w, 1)
    else
      (* The current part has paid each child's size (the child was built in it, or [certify] charged its full
         size again on reuse) and this node's step, all within its budget of at most [max_int] steps: so the
         sums of sizes below, each at most what this part paid, cannot overflow. *)
      let sub = certify st (depth + 1) in
      let step lemma m =
        Option.map
          (fun (vm, pm, sm) -> (v, app lemma [| m; n_literal nt vm; w; pm; refl_n nt w |], sm + 1))
          (sub m)
      in
      (match nat_form st depth t with
      | Some Zero -> Some (v, refl_n nt w, 1)
      | Some (Succ m) -> step nt.nt_succ_step m
      | Some (Double m) -> step nt.nt_double_step m
      | Some (Unfold b) ->
        Option.map (fun (_, pb, sb) -> (v, app nt.nt_unfold_step [| t; b; w; refl_nat nt t; pb |], sb + 1)) (sub b)
      | Some (Op (row, f, a, b)) ->
        (match (lemma_of st row.spec.op, sub a, sub b) with
        | Some (g, hg), Some (va, pa, sa), Some (vb, pb, sb) ->
          let hfg = lam2 nt (refl_nat nt (app (lift_ch st depth 2 f) [| r2; r1 |])) in
          let hn = lib_term row.spec.n_fun in
          Some
            ( v,
              app nt.nt_op_step
                [| f; g; hn; hfg; hg; a; b; n_literal nt va; n_literal nt vb; w; pa; pb; refl_n nt w |],
              sa + sb + 1 )
        | _ -> None)
      | None -> None)

(* The generated lemmas, per pair of terms: a later argument with the same two terms reuses the lemma. The
   cache lasts as long as the Rocq file (document) that runs the imports. *)
let lemma_cache : ((Constr.t * Constr.t) * Constant.t) list ref = Summary.ref ~name:"lean-nat-eq-lemmas" []

(* The most nodes the optional diagnostics print of their terms. *)
let print_bound = 256

exception Too_large

(* Whether the terms [cs] have at most [print_bound] nodes in all: a walk that stops after that many. *)
let printable cs =
  let left = ref print_bound in
  let rec visit c =
    decr left;
    if !left < 0 then raise_notrace Too_large;
    Constr.iter visit c
  in
  try
    List.iter visit cs;
    true
  with Too_large -> false

(* The line about a generated lemma [id : x = y] the kernel refuses with [e]: the statement only when it is
   small enough to print, and the kernel's error only when the proof is too. *)
let refused_lemma_msg id x y proof e =
  if printable [ x; y ] then
    let env = Global.env () in
    let pr = Printer.pr_constr_env env (Evd.from_env env) in
    Pp.(
      str "the generated lemma " ++ Id.print id ++ str " : " ++ pr x ++ str " = " ++ pr y ++ str " is refused by the kernel"
      ++ (if printable [ proof ] then str ": " ++ CErrors.print e
          else str " (its proof has more than " ++ int print_bound ++ str " nodes: the kernel's error is not printed)"))
  else
    Pp.(
      str "the generated lemma " ++ Id.print id ++ str " is refused by the kernel (its statement has more than "
      ++ int print_bound ++ str " nodes and is not printed)")

(* Declare [proof] as the lemma [x = y] (src/Lean.v's [eq] at Nat), named [<entry>__nat_eq_<k>] or, when that
   name is taken, the next free one as [Namegen] counts them (each name it tries charged), and keep it for a
   later place with the same two terms. A lemma the kernel refuses is logged and not used. *)
let declare_nat_eq st x y proof =
  let nt = st.refs in
  let eq = Constr.mkIndU (nt.nt_eq, UVars.Instance.of_array ([||], [| Univ.Level.set |])) in
  let ty = app eq [| nat_type nt; x; y |] in
  st.next <- st.next + 1;
  let id = Id.of_string (Id.to_string st.entry ^ "__nat_eq_" ^ string_of_int st.next) in
  let taken id =
    tick st 1;
    Global.exists_objlabel id
  in
  let id = if taken id then Namegen.next_ident_away_from id taken else id in
  match st.ctx.declare id ty proof with
  | GlobRef.ConstRef c ->
    lemma_cache := ((x, y), c) :: !lemma_cache;
    Some c
  | GlobRef.VarRef _ | GlobRef.IndRef _ | GlobRef.ConstructRef _ -> assert false
  | exception e when CErrors.noncritical e ->
    st.ctx.log (refused_lemma_msg id x y proof e);
    None

(* The lemma of the file's cache for [x] and [y], each entry looked at charged. *)
let cached_nat_eq st depth x y =
  let rec find = function
    | [] -> None
    | ((x', y'), c) :: rest ->
      tick st 1;
      if equal st depth x x' && equal st depth y y' then Some c else find rest
  in
  find !lemma_cache

(* Whether [x] and [y] are closed and use only declared universes; Rocq's walk of both for their universes is
   paid first. *)
let lemma_terms_ok st depth x y =
  closed st depth x && closed st depth y
  &&
  (pay st (add_size (size st depth x) (size st depth y));
   let levels = Vars.universes_of_constr ~init:(Vars.universes_of_constr x) y in
   Result.is_ok (UGraph.check_declared_universes (Global.universes ()) levels))

(* The lemma [x = y] for two closed Nat terms of equal value, generated and declared on first use, at the
   nesting [depth] of the place that needs it: its proof goes through Rocq's binary [N]. *)
let nat_eq_lemma st depth x y =
  match cached_nat_eq st depth x y with
  | Some c -> Some c
  | None ->
    if not (lemma_terms_ok st depth x y) then None
    else
      match (certify st depth x, certify st depth y) with
      | Some (vx, cx, _), Some (vy, cy, _) when Z.equal vx vy ->
        declare_nat_eq st x y (app st.refs.nt_nat_eq [| x; y; n_literal st.refs vx; cx; cy |])
      | _ -> None

(* The lemma [x = y] for the Nat values [x] and [y] of the [Fin] at the bottom of two closed terms (see
   [fin_hole]): its proof is [eq_refl x], which the kernel checks by converting [x] with [y] on their own,
   where it computes [t % 2 ^ 32] directly. *)
let fin_eq_lemma st depth x y =
  match cached_nat_eq st depth x y with
  | Some c -> Some c
  | None ->
    if not (lemma_terms_ok st depth x y) then None
    else
      let nt = st.refs in
      let refl = Constr.mkConstructU ((nt.nt_eq, 1), UVars.Instance.of_array ([||], [| Univ.Level.set |])) in
      declare_nat_eq st x y (app refl [| nat_type nt; x |])

(* A closed term reduced to a [Fin] (src/Lean.v's, Lean's [Fin] predeclared) through records of one field
   each ([UInt32.ofBitVec], [BitVec.ofFin]): those constructors with their arguments but the last, outermost
   first, and the [Fin_mk] constructor with its bound, value and proof. *)
type fin_side = {
  spine : (Constr.t * Constr.t array) list;
  fin_mk : Constr.t;
  bound : Constr.t;
  fval : Constr.t;
  fprf : Constr.t;
}

(* A place of an argument's type [a] and its expected type [d]: two closed Nat terms of equal value ([Nat_hole]),
   or two closed terms that reduce to the same constructors down to a [Fin] whose values are closed Nat terms of
   equal value ([Fin_hole]). *)
type hole = Nat_hole of Constr.t * Constr.t | Fin_hole of { fa : Constr.t; fd : Constr.t; sa : fin_side; sd : fin_side }

let hole_terms = function Nat_hole (x, y) -> (x, y) | Fin_hole { fa; fd; _ } -> (fa, fd)

(* Two closed Nat terms of different values: the types cannot be converted, the argument is left as is. *)
exception Other_values

(* The most records of one field [fin_spine] goes through above the [Fin]: zero to four; a fifth gives no hole. *)
let max_spine = 4

(* The most reduction steps that [whd] takes on one term, in all its head reductions together (the term's own,
   the subject of each projection, and, in [fin_spine], the field of each record it goes through). A step is
   the unfolding of a constant, the substitution of one binder (beta: a constant applied to three arguments it
   binds takes four steps), a zeta step, a cast, a local definition, or a projection (taken before its subject
   is reduced). Each is also charged to the budget. *)
let max_head_steps = 64

(* Whether [ind] has one constructor with one field (after its parameters), and is not mutual. *)
let one_field_record st ind =
  tick st (map_steps st.n_records);
  match Indmap_env.find_opt ind st.records with
  | Some b -> b
  | None ->
    let mib, mip = Inductive.lookup_mind_specif st.genv ind in
    let b =
      Array.length mib.Declarations.mind_packets = 1
      && Array.length mip.Declarations.mind_consnames = 1
      && mip.Declarations.mind_consnrealargs.(0) = 1
    in
    tick st (map_steps st.n_records);
    st.records <- Indmap_env.add ind b st.records;
    st.n_records <- st.n_records + 1;
    b

(* [c] in [env] reduced at its head, [n] steps taken before: by unfolding a constant (not an opaque one),
   beta, zeta, a cast, a local definition of [env], and projecting a constructor's field. The result has the
   number of steps after, which counts the steps that reduce the subject of a projection too, and the head and
   arguments where it stops. A projection's step is taken before its subject is reduced, and the subject is one
   level deeper ([depth]), so that a nest of projections stops at [max_head_steps] steps. [None] at a projection
   of anything but a constructor, or once the term would take more than [max_head_steps] steps: the count is
   checked before each step's substitution. Unlike [Reductionops.whd_all] it reduces no match or fixpoint, and
   every step and every substitution and copy is charged. *)
let rec whd st env depth n c =
  tick st 1;
  check_depth depth;
  if n > max_head_steps then None
  else
    let h, args = Constr.decompose_app c in
    match Constr.kind h with
    | Constr.Const cu -> (
      if n + 1 > max_head_steps then None
      else
        match const_body st depth ~nat:false cu with
        | Some body -> whd_beta st env depth (n + 1) body args
        | None -> Some (n, h, args))
    | Constr.Lambda _ when Array.length args > 0 -> whd_beta st env depth n h args
    | Constr.LetIn (_, v, _, b) ->
      if n + 1 > max_head_steps then None else whd st env depth (n + 1) (app_ch st (subst1_ch st depth v b) args)
    | Constr.Cast (c, _, _) -> if n + 1 > max_head_steps then None else whd st env depth (n + 1) (app_ch st c args)
    | Constr.Proj (p, _, s) -> (
      match whd st env (depth + 1) (n + 1) s with
      | Some (n, sh, sargs) when Constr.isConstruct sh ->
        let i = Projection.npars p + Projection.arg p in
        if i < Array.length sargs && n <= max_head_steps then whd st env depth n (app_ch st sargs.(i) args) else None
      | _ -> None)
    | Constr.Rel k -> (
      match Environ.lookup_rel k env with
      | Context.Rel.Declaration.LocalDef (_, b, _) ->
        if n + 1 > max_head_steps then None else whd st env depth (n + 1) (app_ch st (lift_ch st depth k b) args)
      | Context.Rel.Declaration.LocalAssum _ -> Some (n, h, args)
      | exception Not_found -> None)
    | _ -> Some (n, h, args)

(* [f] applied to [args]: each leading lambda of [f] takes an argument, one step each, the count checked before
   the binder is taken; then one substitution of the arguments taken, and the rest applied. *)
and whd_beta st env depth n f args =
  let nargs = Array.length args in
  let rec peel f k =
    if k = nargs then Some (f, k)
    else
      match Constr.kind f with
      | Constr.Lambda (_, _, b) ->
        if n + k + 1 > max_head_steps then None
        else begin
          tick st 1;
          peel b (k + 1)
        end
      | _ -> Some (f, k)
  in
  match peel f 0 with
  | None -> None
  | Some (body, k) ->
    let c = subst_args st depth body args k in
    let c = if k = nargs then c else if k = 0 then app_ch st c args else app_ch st c (sub_ch st args k (nargs - k)) in
    whd st env depth (n + k) c

(* [c], closed, reduced at its head ([whd]) until a constructor heads it; [None] at anything else. *)
let head_reduce st depth steps c =
  match whd st st.genv depth steps c with
  | Some (n, h, args) when Constr.isConstruct h -> Some (n, h, args)
  | Some _ | None -> None

(* [c] reduced through at most [max_spine] records of one field to a [Fin], [n] records and [steps] reduction
   steps of the side already taken. *)
let rec fin_spine st depth n steps c acc =
  tick st 1;
  check_depth depth;
  if n > max_spine then None
  else
    match head_reduce st depth steps c with
    | None -> None
    | Some (steps, h, args) -> (
      match Constr.kind h with
      | Constr.Construct ((ind, 1), _) when Ind.CanOrd.equal ind st.refs.nt_fin && Array.length args = 3 ->
        Some { spine = List.rev acc; fin_mk = h; bound = args.(0); fval = args.(1); fprf = args.(2) }
      | Constr.Construct ((ind, 1), _) when one_field_record st ind && Array.length args >= 1 ->
        let k = Array.length args - 1 in
        fin_spine st (depth + 1) (n + 1) steps args.(k) ((h, sub_ch st args 0 k) :: acc)
      | _ -> None)

(* The value of the closed Nat term [c] for [fin_hole], which reads [Nat.mod] and [HMod.hMod] at Nat's instance
   too. The kernel checks a Fin lemma by computing both sides on the unary [Nat], in time that grows with each
   number it computes but a divisor ([Nat.mod n m] compares [m] with [n], which stops at [n]); so [c] and every
   operand it reads, but a divisor, are below [fin_ceiling]. [None] otherwise. Each term (or constant) is
   computed again only when its slot of the memo holds another term, and each computation is charged. *)
let rec fin_value st depth c =
  match memo_find st st.fin_values st.const_fin_values c with
  | Some v -> v
  | None ->
    let v = fin_value_node st depth c in
    memo_add st st.fin_values st.const_fin_values c v;
    v

and fin_value_node st depth c =
  tick st 1;
  check_depth depth;
  let below v = if Z.lt v fin_ceiling then Some v else None in
  let rem x y =
    match (fin_value st (depth + 1) x, value st (depth + 1) y) with
    | Some x, Some y when Z.sign y > 0 -> below (Z.rem x y)
    | _ -> None
  in
  let operands_below xs = List.for_all (fun x -> Option.has_some (fin_value st (depth + 1) x)) xs in
  let h, args = Constr.decompose_app c in
  match Constr.kind h with
  | Constr.Const (k, _)
    when Array.length args = 6 && mem_const st k st.hmods && is_nat_ind st args.(0) && is_nat_ind st args.(1)
         && is_nat_ind st args.(2) && pat_matches st st.hmod_nat args.(3) ->
    rem args.(4) args.(5)
  | Constr.Const (k, _) when Array.length args = 2 && mem_const st k st.mods -> rem args.(0) args.(1)
  | _ -> (
    match nat_form st depth c with
    | Some (Unfold b) -> fin_value st (depth + 1) b
    | Some (Succ x) ->
      (* [c] is [Nat_succ] applied [j] times to [b]: every operand of the run is below the ceiling when [b] has a
         Fin value and [c]'s value, the largest of the run, is below it *)
      let b, j = succ_run st x 1 in
      if Option.has_some (fin_value st (depth + 1) b) then
        Option.bind (value st (depth + 1) b) (fun v -> below (Z.add v (Z.of_int j)))
      else None
    | Some (Double x) -> if operands_below [ x ] then Option.bind (value st depth c) below else None
    | Some (Op (_, _, x, y)) -> if operands_below [ x; y ] then Option.bind (value st depth c) below else None
    | Some Zero | None -> Option.bind (value st depth c) below)

let same_constructor c c' =
  match (Constr.kind c, Constr.kind c') with
  | Constr.Construct (k, _), Constr.Construct (k', _) -> Construct.CanOrd.equal k k'
  | _ -> false

let head_const c = match Constr.kind (fst (Constr.decompose_app c)) with Constr.Const (k, _) -> Some k | _ -> None

(* The rule of the Fin case (README, "Transport of proof arguments across Nat literals"): [a] (in the
   argument's type) and [d] (in the expected type) are a [Fin_hole] when both are closed, their head constants
   differ, both reduce (at most [max_head_steps] steps each side, all its head reductions together) through
   the same records of one field, with the same parameters, to a [Fin] of the same bound, and the two [Fin]
   values are closed Nat terms of equal value that are not the same term. [Other_values] when those values
   differ: the kernel refuses the argument as without the pass. [None] in every other case: the pass looks
   inside them as before. Closedness and every comparison are charged. *)
let fin_hole st depth a d =
  match (head_const a, head_const d) with
  | Some ka, Some kd when (not (Constant.CanOrd.equal ka kd)) && closed st depth a && closed st depth d -> (
    match (fin_spine st depth 0 0 a [], fin_spine st depth 0 0 d []) with
    | Some sa, Some sd
      when List.length sa.spine = List.length sd.spine
           && List.for_all2
                (fun (c, ps) (c', ps') ->
                  tick st 1;
                  same_constructor c c'
                  && Array.length ps = Array.length ps'
                  && Array.for_all2 (equal st depth) ps ps')
                sa.spine sd.spine
           && equal st depth sa.bound sd.bound ->
      (match (fin_value st depth sa.fval, fin_value st depth sd.fval) with
      | Some va, Some vd ->
        if not (Z.equal va vd) then raise Other_values
        else if equal st depth sa.fval sd.fval then None
        else Some (Fin_hole { fa = a; fd = d; sa; sd })
      | _ -> None)
    | _ -> None)
  | _ -> None

(* Where two types differ: [Keep] takes the expected type's subterm (a difference there is the kernel's to
   convert, as without the pass), [Hole k] the [k]th hole. *)
type nat_shape =
  | Keep
  | Hole of int
  | App_s of nat_shape * nat_shape array
  | Prod_s of nat_shape * nat_shape
  | Lambda_s of nat_shape * nat_shape
  | LetIn_s of nat_shape * nat_shape * nat_shape
  | Proj_s of nat_shape

let is_keep = function Keep -> true | _ -> false

(* The shape of the differences of [a] (the argument's type) and [d] (the expected type), and its holes: pairs
   [(x, y)] of closed Nat terms ([x] in [a], [y] in [d]) of equal value from [transport_min] on, [y] not the
   same literal as [x], and the places of [fin_hole]. [depth] is the nesting of the place the types come from.
   A hole equal to an earlier one is that one; each earlier hole compared is charged. *)
let nat_diff st depth a d =
  let pairs = ref [] and count = ref 0 in
  let add depth h =
    let x, y = hole_terms h in
    let rec find = function
      | [] -> None
      | (k, h') :: rest ->
        tick st 1;
        let x', y' = hole_terms h' in
        if equal st depth x x' && equal st depth y y' then Some k else find rest
    in
    match find !pairs with
    | Some k -> Hole k
    | None ->
      let k = !count in
      incr count;
      pairs := (k, h) :: !pairs;
      Hole k
  in
  let nat_pair depth a d =
    match (value st depth a, value st depth d) with
    | None, _ | _, None -> None
    | Some va, Some vd ->
      if not (Z.equal va vd) then raise Other_values
      else if Z.lt va transport_min || equal st depth a d then Some Keep
      else
        match (literal_of st depth a, literal_of st depth d) with
        | Some la, Some ld when equal st depth la ld -> Some Keep
        | _ -> Some (add depth (Nat_hole (a, d)))
  in
  let rec go depth a d =
    tick st 1;
    check_depth depth;
    if a == d then Keep
    else
      match nat_pair depth a d with
      | Some s -> s
      | None ->
      match fin_hole st depth a d with
      | Some h -> add depth h
      | None ->
        let go = go (depth + 1) in
        (match (Constr.kind a, Constr.kind d) with
        | Constr.App _, Constr.App _ ->
          let ha, aa = Constr.decompose_app a and hd, ad = Constr.decompose_app d in
          if Array.length aa <> Array.length ad then Keep
          else
            let sh = go ha hd in
            tick st (Array.length aa);
            let sargs = Array.map2 go aa ad in
            if is_keep sh && Array.for_all is_keep sargs then Keep else App_s (sh, sargs)
        | Constr.Prod (_, a1, a2), Constr.Prod (_, d1, d2) ->
          let s1 = go a1 d1 in
          let s2 = go a2 d2 in
          if is_keep s1 && is_keep s2 then Keep else Prod_s (s1, s2)
        | Constr.Lambda (_, a1, a2), Constr.Lambda (_, d1, d2) ->
          let s1 = go a1 d1 in
          let s2 = go a2 d2 in
          if is_keep s1 && is_keep s2 then Keep else Lambda_s (s1, s2)
        | Constr.LetIn (_, a1, a2, a3), Constr.LetIn (_, d1, d2, d3) ->
          let s1 = go a1 d1 in
          let s2 = go a2 d2 in
          let s3 = go a3 d3 in
          if is_keep s1 && is_keep s2 && is_keep s3 then Keep else LetIn_s (s1, s2, s3)
        | Constr.Proj (pa, _, a1), Constr.Proj (pd, _, d1) when Projection.CanOrd.equal pa pd ->
          let s1 = go a1 d1 in
          if is_keep s1 then Keep else Proj_s s1
        | _ -> Keep)
  in
  let shape = go depth a d in
  let holes = Array.make !count (Nat_hole (a, d)) in
  List.iter (fun (k, h) -> holes.(k) <- h) !pairs;
  (shape, holes)

(* [d] with each hole [k] at binder depth [depth] replaced by [hole k depth], each node it rebuilds charged. *)
let rec nat_fill st shape d depth hole =
  tick st 1;
  match (shape, Constr.kind d) with
  | Keep, _ -> d
  | Hole k, _ -> hole k depth
  | App_s (sh, sargs), _ ->
    let h, args = Constr.decompose_app d in
    tick st (Array.length args);
    app_ch st (nat_fill st sh h depth hole) (Array.map2 (fun s c -> nat_fill st s c depth hole) sargs args)
  | Prod_s (s1, s2), Constr.Prod (na, t, b) ->
    Constr.mkProd (na, nat_fill st s1 t depth hole, nat_fill st s2 b (depth + 1) hole)
  | Lambda_s (s1, s2), Constr.Lambda (na, t, b) ->
    Constr.mkLambda (na, nat_fill st s1 t depth hole, nat_fill st s2 b (depth + 1) hole)
  | LetIn_s (s1, s2, s3), Constr.LetIn (na, v, t, b) ->
    Constr.mkLetIn (na, nat_fill st s1 v depth hole, nat_fill st s2 t depth hole, nat_fill st s3 b (depth + 1) hole)
  | Proj_s s1, Constr.Proj (p, r, c) -> Constr.mkProj (p, r, nat_fill st s1 c depth hole)
  | (Prod_s _ | Lambda_s _ | LetIn_s _ | Proj_s _), _ -> assert false

exception Found

(* Whether [c], at the nesting [depth], has a closed Nat subterm of value [transport_min] or more. *)
let has_big_nat st depth c =
  let rec scan depth c =
    tick st 1;
    check_depth depth;
    match value st depth c with
    | Some v -> if Z.geq v transport_min then raise_notrace Found
    | None -> Constr.iter (scan (depth + 1)) c
  in
  try
    scan depth c;
    false
  with Found -> true

(* Whether the constant [k]'s declared type ends in a record of one field ([UInt32], [BitVec w]): its
   declaration read directly, each product it goes through charged. *)
let fin_typed_const st k =
  match table_find st st.fin_consts k with
  | Some b -> b
  | None ->
    tick st 1;
    let rec concl depth ty =
      tick st 1;
      check_depth depth;
      match Constr.kind ty with
      | Constr.Prod (_, _, b) | Constr.Cast (b, _, _) -> concl (depth + 1) b
      | _ -> (
        match Constr.kind (fst (Constr.decompose_app ty)) with
        | Constr.Ind (ind, _) -> one_field_record st ind
        | _ -> false)
    in
    let b =
      match Environ.lookup_constant_opt k st.genv with
      | Some cb -> concl 0 cb.Declarations.const_type
      | None -> false
    in
    table_add st st.fin_consts k b;
    b

(* The gate of the Fin case: whether [c], at the nesting [depth], has a closed application of a constant whose
   type ends in a record of one field, or [OfNat.ofNat] at such a record. The Nat case keeps [has_big_nat]. *)
let has_fin_site st depth c =
  let rec scan depth c =
    tick st 1;
    check_depth depth;
    (match Constr.kind c with
    | Constr.App (h, args) -> (
      match Constr.kind h with
      | Constr.Const (k, _) ->
        let site =
          if mem_const st k st.of_nat then
            Array.length args = 3
            && (match Constr.kind (fst (Constr.decompose_app args.(0))) with
               | Constr.Ind (ind, _) -> one_field_record st ind
               | _ -> false)
          else fin_typed_const st k
        in
        if site && closed st depth c then raise_notrace Found
      | _ -> ())
    | _ -> ());
    Constr.iter (scan (depth + 1)) c
  in
  try
    scan depth c;
    false
  with Found -> true

let has_beta_redex st depth c =
  let rec scan depth c =
    tick st 1;
    check_depth depth;
    match Constr.kind c with
    | Constr.App (h, _) when Constr.isLambda h -> raise_notrace Found
    | _ -> Constr.iter (scan (depth + 1)) c
  in
  try
    scan depth c;
    false
  with Found -> true

(* The beta normal form of [c], by its syntax: the head and arguments of an application first, then each
   redex contracted by the charged substitution, and its result normalized again. It unfolds no constant.
   A beta normal form depends on the term only, so it is kept per term, and a term already normal is found
   again at its next occurrence. A run of applications of closed leaves ([unary_run]) is normal down to its
   base, so only the base is normalized, and the run is copied (each application charged) only when the base
   changes. *)
let rec nf_beta st depth c =
  if is_leaf c then c
  else
    match memo_get st st.normal c with
    | Some r -> r
    | None ->
      check_depth depth;
      let r =
        match unary_run st c 0 with
        | b, j when j > 0 ->
          let b' = nf_beta st (depth + 1) b in
          if b' == b then c
          else
            let rec copy c =
              if c == b then b'
              else
                match Constr.kind c with
                | Constr.App (h, [| x |]) ->
                  tick st (node_steps c);
                  Constr.mkApp (h, [| copy x |])
                | _ -> assert false
            in
            copy c
        | _ -> (
          tick st (node_steps c);
          match Constr.kind c with
          | Constr.App (f, args) -> (
            let f' = nf_beta st (depth + 1) f in
            let args' = CArray.Smart.map (nf_beta st (depth + 1)) args in
            match Constr.kind f' with
            | Constr.Lambda _ -> nf_beta st (depth + 1) (contract st depth f' args')
            | _ -> if f' == f && args' == args then c else app_ch st f' args')
          | _ -> Constr.map (nf_beta st (depth + 1)) c)
      in
      memo_put st st.normal c r;
      if r != c then memo_put st st.normal r r;
      r

(* [f] applied to [args], each leading lambda of [f] taking an argument. *)
and contract st depth f args =
  let nargs = Array.length args in
  let rec peel f k =
    if k = nargs then (f, k)
    else
      match Constr.kind f with
      | Constr.Lambda (_, _, b) ->
        tick st 1;
        peel b (k + 1)
      | _ -> (f, k)
  in
  let body, k = peel f 0 in
  let c = subst_args st depth body args k in
  if k = nargs then c else app_ch st c (sub_ch st args k (nargs - k))

let beta st depth c = if has_beta_redex st depth c then nf_beta st depth c else c

let is_irrelevant_binder na =
  match Context.binder_relevance na with Sorts.Irrelevant -> true | Sorts.Relevant | Sorts.RelevanceVar _ -> false

(* The declared types of globals at a universe instance, read from their declarations; [None] for a template
   inductive type, whose type Rocq computes from its arguments. *)
let const_type st depth k u =
  tick st 1;
  Option.map (fun cb -> instantiate st depth u cb.Declarations.const_type) (Environ.lookup_constant_opt k st.genv)

let ind_type st depth ind u =
  tick st 1;
  let mib, mip = Inductive.lookup_mind_specif st.genv ind in
  match mib.Declarations.mind_template with
  | Some _ -> None
  | None -> Some (instantiate st depth u mip.Declarations.mind_user_arity)

let ctor_type st depth (ind, i) u =
  tick st 1;
  let mib, mip = Inductive.lookup_mind_specif st.genv ind in
  match mib.Declarations.mind_template with
  | Some _ -> None
  | None -> Some (instantiate st depth u mip.Declarations.mind_user_lc.(i - 1))

(* [ty] in [env] reduced at its head ([whd]) to a product, or to a sort; [None] when [whd] does not get there. *)
let expose_prod st env depth ty =
  match whd st env depth 0 ty with
  | Some (_, h, [||]) when Constr.isProd h -> Some h
  | Some _ | None -> None

let expose_sort st env depth ty =
  match whd st env depth 0 ty with
  | Some (_, h, [||]) when Constr.isSort h -> Some (Constr.destSort h)
  | Some _ | None -> None

(* The type of [c] in [env], as [Retyping.get_type_of] gives it for the terms it reads: a variable's declared
   type, a global's declared type at its universe instance, the type of an application with its arguments
   substituted (a product exposed by [expose_prod] when the type is not one), of a lambda, of a let, of a cast
   and of a projection of a record (its record type exposed by [whd]). [None] for every other term, and when a
   type it needs is not exposed: no type is guessed and Rocq's unrestricted reduction is never called. *)
let rec type_of st env depth c =
  tick st 1;
  check_depth depth;
  match Constr.kind c with
  | Constr.Rel k -> (
    match Environ.lookup_rel k env with
    | decl -> Some (lift_ch st depth k (Context.Rel.Declaration.get_type decl))
    | exception Not_found -> None)
  | Constr.Const (k, u) -> const_type st depth k u
  | Constr.Ind (ind, u) -> ind_type st depth ind u
  | Constr.Construct (cstr, u) -> ctor_type st depth cstr u
  | Constr.App (f, args) -> Option.bind (type_of st env (depth + 1) f) (fun ty -> apply_type st env depth ty args)
  | Constr.Lambda (na, t, b) ->
    Option.map
      (fun tb -> Constr.mkProd (na, t, tb))
      (type_of st (Environ.push_rel (Context.Rel.Declaration.LocalAssum (na, t)) env) (depth + 1) b)
  | Constr.LetIn (na, v, t, b) ->
    Option.map (subst1_ch st depth v)
      (type_of st (Environ.push_rel (Context.Rel.Declaration.LocalDef (na, v, t)) env) (depth + 1) b)
  | Constr.Cast (_, _, t) -> Some t
  | Constr.Proj (p, _, s) -> (
    match Option.bind (type_of st env (depth + 1) s) (whd st env (depth + 1) 0) with
    | Some (_, h, params) -> (
      match Constr.kind h with
      | Constr.Ind (ind, u) when Ind.CanOrd.equal ind (Projection.inductive p) ->
        tick st (1 + Array.length params);
        let _, pty = Environ.lookup_projection p env in
        Some (substl_ch st depth (s :: List.rev (Array.to_list params)) (instantiate st depth u pty))
      | _ -> None)
    | None -> None)
  | Constr.Var _ | Constr.Meta _ | Constr.Evar _ | Constr.Sort _ | Constr.Prod _ | Constr.Case _ | Constr.Fix _
  | Constr.CoFix _ | Constr.Int _ | Constr.Float _ | Constr.String _ | Constr.Array _ ->
    None

(* [ty], the type of a function, applied to [args]: its products take them, each charged, and the arguments
   are substituted at the end or where a product must be exposed. *)
and apply_type st env depth ty args =
  let n = Array.length args in
  let rec loop i ty subst =
    if i = n then Some (substl_ch st depth subst ty)
    else begin
      tick st 1;
      match Constr.kind ty with
      | Constr.Prod (_, _, b) -> loop (i + 1) b (args.(i) :: subst)
      | _ -> (
        match expose_prod st env depth (substl_ch st depth subst ty) with
        | Some p -> loop i p []
        | None -> None)
    end
  in
  loop 0 ty []

(* The relevance of the type [ty] in [env]: that of its sort, which [type_of] and [expose_sort] read, a product
   having the relevance of its codomain; [None] when it cannot be read. *)
let rec type_relevance st env depth ty =
  tick st 1;
  check_depth depth;
  match Constr.kind ty with
  | Constr.Prod (na, t, b) ->
    type_relevance st (Environ.push_rel (Context.Rel.Declaration.LocalAssum (na, t)) env) (depth + 1) b
  | _ ->
    Option.map Sorts.relevance_of_sort (Option.bind (type_of st env depth ty) (expose_sort st env depth))

(* The type of the proof field of [side]'s [Fin_mk] at the value [z], from the constructor's declared type. *)
let fin_proof_type st depth side z =
  let (ind, i), u = Constr.destConstruct side.fin_mk in
  let field ty =
    match Constr.kind ty with
    | Constr.Prod (_, _, b) -> (
      match Constr.kind b with
      | Constr.Prod (_, _, b) -> (
        match Constr.kind b with Constr.Prod (_, t, _) -> Some t | _ -> None)
      | _ -> None)
    | _ -> None
  in
  match Option.bind (ctor_type st depth (ind, i) u) field with
  | Some t -> substl_ch st depth [ z; side.bound ] t
  | None -> invalid_arg "fin_proof_type"

(* Record the lemma [id] an argument uses, once, in the order of first use. *)
let add_lemma_id st id =
  tick st (2 * map_steps st.n_lemma_ids);
  if not (Id.Set.mem id st.lemma_ids) then begin
    st.lemma_ids <- Id.Set.add id st.lemma_ids;
    st.n_lemma_ids <- st.n_lemma_ids + 1;
    st.lemmas <- id :: st.lemmas
  end

(* [arg], whose expected type is the SProp type [dom], at the nesting [depth], cast along the lemmas of its
   holes, or [None] when its type differs from [dom] at no hole. *)
let rec transport_arg st env depth arg dom =
  (* Each argument it looks at has a budget of its own, which [Out_of_budget] ends like the entry's; its steps
     count toward the entry's total too. *)
  let entry_steps = st.steps in
  st.steps <- budget ();
  match transport_arg_in st env depth arg dom with
  | r ->
    st.steps <- entry_steps;
    r
  | exception e ->
    st.steps <- entry_steps;
    Exninfo.iraise (Exninfo.capture e)

and transport_arg_in st env depth arg dom =
  let dom = beta st depth dom in
  if not (has_big_nat st depth dom || has_fin_site st depth dom) then None
  else
    match Option.map (fun ty -> nat_diff st depth (beta st depth ty) dom) (type_of st env depth arg) with
    | exception Other_values -> None
    | None | Some (_, [||]) -> None
    | Some (shape, holes) ->
      let lemmas =
        Array.map
          (function
            | Nat_hole (x, y) -> nat_eq_lemma st depth x y
            | Fin_hole { sa; sd; _ } -> fin_eq_lemma st depth sa.fval sd.fval)
          holes
      in
      if Array.exists Option.is_empty lemmas then None
      else begin
        let nt = st.refs in
        (* [dom] under the motive's one or two binders, lifted once each for all the holes. *)
        let dom1 = lazy (lift_ch st depth 1 dom) and dom2 = lazy (lift_ch st depth 2 dom) in
        let side k j = if j < k then snd (hole_terms holes.(j)) else fst (hole_terms holes.(j)) in
        let cast p k hole =
          tick st 1;
          let lemma = Constr.mkConstU (Option.get lemmas.(k), UVars.Instance.empty) in
          match hole with
          | Nat_hole (x, y) ->
            let body =
              nat_fill st shape (Lazy.force dom1) 0 (fun j depth -> if j = k then Constr.mkRel (depth + 1) else side k j)
            in
            let motive = Constr.mkLambda (Context.anonR, nat_type nt, body) in
            app nt.nt_transport [| motive; x; y; lemma; p |]
          | Fin_hole { sa; sd; _ } ->
            (* [sprop_transport (fun z => forall hz, D[mk z hz]) va vd lemma (fun hz => p) proof]: [mk] is [d]'s
               constructors down to its [Fin_mk], [proof] the proof of [d]'s [Fin]. *)
            let mk v prf =
              List.fold_right
                (fun (c, params) inner ->
                  tick st (Array.length params + 1);
                  app c (Array.append params [| inner |]))
                sd.spine
                (app sd.fin_mk [| sd.bound; v; prf |])
            in
            let body =
              nat_fill st shape (Lazy.force dom2) 0 (fun j depth ->
                  if j = k then mk (Constr.mkRel (depth + 2)) (Constr.mkRel (depth + 1)) else side k j)
            in
            let hz = Context.make_annot (Name (Id.of_string "hz")) Sorts.Irrelevant in
            let motive =
              Constr.mkLambda
                ( Context.nameR (Id.of_string "z"),
                  nat_type nt,
                  Constr.mkProd (hz, fin_proof_type st depth sd (Constr.mkRel 1), body) )
            in
            let lam = Constr.mkLambda (hz, fin_proof_type st depth sd sa.fval, lift_ch st depth 1 p) in
            app (app nt.nt_transport [| motive; sa.fval; sd.fval; lemma; lam |]) [| sd.fprf |]
        in
        let p = ref arg in
        Array.iteri (fun k h -> p := cast !p k h) holes;
        st.count <- st.count + 1;
        Array.iter (fun c -> add_lemma_id st (Constant.label (Option.get c))) lemmas;
        Some !p
      end

(* Whether [f] applied to [args] is [Nat_succ] or [Nat_double] applied to one argument, whose declared types
   [setup] has read once to be one relevant Nat argument to Nat: such an application has no SProp argument, so
   [transport_walk] reads no type for it and peels no product (it still walks the argument). *)
let unary_nat_head st f args =
  Array.length args = 1
  &&
  match Constr.kind f with
  | Constr.Construct ((ind, 2), _) -> st.unary_succ && Ind.CanOrd.equal ind st.refs.nt_nat
  | Constr.Const (k, _) -> st.unary_double && Constant.CanOrd.equal k st.refs.nt_double
  | _ -> false

(* [args], the arguments of [f] at the nesting [depth], each SProp argument transported where it needs it.
   [f]'s type is read by [type_of]; each product it goes through is charged, and the arguments before it are
   substituted into a domain only for an SProp binder, and into the rest where a product must be exposed. *)
let transport_args st env depth f args =
  let n = Array.length args in
  let out = ref args in
  let set k a =
    if !out == args then begin
      tick st n;
      out := Array.copy args
    end;
    !out.(k) <- a
  in
  (* [ty] is the type of [f] applied to the arguments before [k], under their binders: [subst] holds those
     arguments, the last first. *)
  let rec loop k ty subst =
    if k < n then begin
      tick st 1;
      match Constr.kind ty with
      | Constr.Prod (na, dom, codom) ->
        if is_irrelevant_binder na then
          Option.iter (set k) (transport_arg st env depth !out.(k) (substl_ch st depth subst dom));
        loop (k + 1) codom (!out.(k) :: subst)
      | _ -> (
        match expose_prod st env depth (substl_ch st depth subst ty) with
        | Some ty -> loop k ty []
        | None -> ())
    end
  in
  Option.iter (fun ty -> loop 0 ty []) (type_of st env depth f);
  !out

let rec transport_walk st env depth c =
  tick st 1;
  check_depth depth;
  let walk env = transport_walk st env (depth + 1) in
  let push d = Environ.push_rel d env in
  match Constr.kind c with
  | Constr.App (f, args) ->
    let f' = walk env f in
    let args' = smart_map_ch st (walk env) args in
    let args' = if unary_nat_head st f' args' then args' else transport_args st env depth f' args' in
    if f' == f && args' == args then c else app_ch st f' args'
  | Constr.Lambda (na, t, b) ->
    let t' = walk env t in
    let b' = walk (push (Context.Rel.Declaration.LocalAssum (na, t'))) b in
    if t' == t && b' == b then c else Constr.mkLambda (na, t', b')
  | Constr.Prod (na, t, b) ->
    let t' = walk env t in
    let b' = walk (push (Context.Rel.Declaration.LocalAssum (na, t'))) b in
    if t' == t && b' == b then c else Constr.mkProd (na, t', b')
  | Constr.LetIn (na, v, t, b) ->
    let v' = walk env v in
    let t' = walk env t in
    let b' = walk (push (Context.Rel.Declaration.LocalDef (na, v', t'))) b in
    if v' == v && t' == t && b' == b then c else Constr.mkLetIn (na, v', t', b')
  | Constr.Proj (p, r, c0) ->
    let c0' = walk env c0 in
    if c0' == c0 then c else Constr.mkProj (p, r, c0')
  | _ -> c

(* [body], whose declared type is [ty], with its SProp result transported to [ty] under its binders, from the
   nesting [depth]; each binder charged. *)
let rec transport_result st env depth body ty =
  tick st 1;
  check_depth depth;
  match (Constr.kind body, Constr.kind ty) with
  | Constr.Lambda (na, t, b), Constr.Prod (_, _, tb) ->
    let env = Environ.push_rel (Context.Rel.Declaration.LocalAssum (na, t)) env in
    let b' = transport_result st env (depth + 1) b tb in
    if b' == b then body else Constr.mkLambda (na, t, b')
  | _ ->
    let irrelevant =
      (has_big_nat st depth ty || has_fin_site st depth ty)
      &&
      match type_relevance st env depth ty with
      | Some r -> Sorts.relevance_equal Sorts.Irrelevant r
      | None -> false
    in
    if irrelevant then Option.default body (transport_arg st env depth body ty) else body

(* The declared type of a global as its declaration holds it (no instance: the scan below looks for constants
   only). *)
let global_type st g =
  tick st 1;
  match g with
  | GlobRef.ConstRef k -> Option.map (fun cb -> cb.Declarations.const_type) (Environ.lookup_constant_opt k st.genv)
  | GlobRef.IndRef ind ->
    let _, mip = Inductive.lookup_mind_specif st.genv ind in
    Some mip.Declarations.mind_user_arity
  | GlobRef.ConstructRef (ind, i) ->
    let _, mip = Inductive.lookup_mind_specif st.genv ind in
    Some mip.Declarations.mind_user_lc.(i - 1)
  | GlobRef.VarRef _ -> None

(* Whether the entry may need the pass: [ty], [body] or the type of a global they name holds one of the
   triggers (the rows' constants, [Nat_double], which every literal from 5000 on holds) or a constant of
   type Nat of value [transport_min] or more (its declared type read first, so that only a constant of type
   Nat looks up its value). *)
let may_apply st ty body =
  let big_const depth k c =
    tick st 1;
    match Environ.lookup_constant_opt k st.genv with
    | Some cb when is_nat_ind st cb.Declarations.const_type -> (
      match value st depth c with Some v -> Z.geq v transport_min | None -> false)
    | Some _ | None -> false
  in
  let seen = table GlobRef.UserOrd.hash GlobRef.UserOrd.equal in
  let rec scan types depth c =
    tick st 1;
    check_depth depth;
    match Constr.kind c with
    | Constr.Const (k, _) ->
      if Option.has_some (table_find st st.triggers k) || big_const depth k c then raise_notrace Found;
      if types then global depth (GlobRef.ConstRef k)
    | Constr.Ind (ind, _) -> if types then global depth (GlobRef.IndRef ind)
    | Constr.Construct (cs, _) -> if types then global depth (GlobRef.ConstructRef cs)
    | _ -> Constr.iter (scan types (depth + 1)) c
  and global depth g =
    if Option.is_empty (table_find st seen g) then begin
      table_add st seen g ();
      Option.iter (scan false (depth + 1)) (global_type st g)
    end
  in
  try
    scan true 0 ty;
    scan true 0 body;
    false
  with Found -> true

(* The export's constants of the Lean name [path]: the importer collects each instance of the name, charged
   here by the list it gives, one step per instance and one per call. *)
let consts st path =
  let l = st.ctx.consts path in
  tick st (1 + List.length l);
  l

let rec resolve st = function
  | Nat_type -> Nat_type
  | Any -> Any
  | Inst (path, ps) ->
    tick st 1;
    Inst (consts st path, List.map (resolve st) ps)

(* Whether [ty] is one relevant Nat argument to Nat. *)
let one_relevant_nat st ty =
  match Constr.kind ty with
  | Constr.Prod (na, d, c) -> (not (is_irrelevant_binder na)) && is_nat_ind st d && is_nat_ind st c
  | _ -> false

(* The entry's view of the export, charged as the rest of its part: the rows' constants, the constants of the
   Fin case, and the declared types of [Nat_succ] and [Nat_double], read once (see [unary_nat_head]). *)
let setup st =
  let rows =
    List.map
      (fun spec ->
        { spec; funs = consts st spec.fun_name; classes = consts st spec.class_name; inst_pat = resolve st spec.inst })
      op_specs
  in
  st.rows <- rows;
  st.of_nat <- consts st [ "OfNat"; "ofNat" ];
  st.inst_of_nat <- consts st [ "instOfNatNat" ];
  let triggers = table Constant.CanOrd.hash Constant.CanOrd.equal in
  List.iter
    (fun k -> table_add st triggers k ())
    (st.refs.nt_double :: List.concat_map (fun row -> row.funs @ row.classes) rows);
  st.triggers <- triggers;
  st.mods <- consts st [ "Nat"; "mod" ];
  st.hmods <- consts st [ "HMod"; "hMod" ];
  st.hmod_nat <- resolve st (Inst ([ "instHMod" ], [ Nat_type; Inst ([ "Nat"; "instMod" ], []) ]));
  st.unary_succ <-
    (match ctor_type st 0 (st.refs.nt_nat, 2) UVars.Instance.empty with
    | Some ty -> one_relevant_nat st ty
    | None -> false);
  st.unary_double <-
    (match const_type st 0 st.refs.nt_double UVars.Instance.empty with
    | Some ty -> one_relevant_nat st ty
    | None -> false)

let new_state ctx env refs entry =
  {
    ctx;
    refs;
    genv = env;
    rows = [];
    of_nat = [];
    inst_of_nat = [];
    triggers = table Constant.CanOrd.hash Constant.CanOrd.equal;
    mods = [];
    hmods = [];
    hmod_nat = Any;
    lemma_ops = [];
    unary_succ = false;
    unary_double = false;
    records = Indmap_env.empty;
    n_records = 0;
    fin_consts = cmap ();
    entry;
    steps = budget ();
    total = total_budget ();
    values = memo ();
    const_values = cmap ();
    fin_values = memo ();
    const_fin_values = cmap ();
    certs = memo ();
    const_certs = cmap ();
    sizes = memo ();
    free = memo ();
    normal = memo ();
    next = 0;
    count = 0;
    lemmas = [];
    lemma_ids = Id.Set.empty;
    n_lemma_ids = 0;
  }

(* The registrations of the rows' [N] functions and [toN] lemmas. *)
let rows_registered () =
  List.for_all (fun spec -> Rocqlib.has_ref spec.n_fun && Rocqlib.has_ref spec.to_n_lemma) op_specs

let transport ctx env ~entry ty body =
  match refs () with
  | Some refs when rows_registered () -> (
    let st = new_state ctx env refs entry in
    match
      setup st;
      if not (may_apply st ty body) then None
      else
        let body' = transport_result st env 0 (transport_walk st env 0 body) ty in
        (* The list of lemmas has one element per charged insertion of [add_lemma_id]. *)
        if st.count = 0 then None else Some { value = body'; count = st.count; lemmas = List.rev st.lemmas }
    with
    | r -> r
    | exception Out_of_budget ->
      ctx.log
        Pp.(
          str "the transport pass stops: it needs more than " ++ int (budget ()) ++ str " steps or a nesting deeper than "
          ++ int max_depth ++ str "; the value is left as Lean's");
      None
    | exception Out_of_total ->
      ctx.log
        Pp.(
          str "the transport pass stops: it needs more than " ++ int (total_budget ())
          ++ str " steps in total; the value is left as Lean's");
      None
    | exception e when CErrors.noncritical e ->
      ctx.log Pp.(str "the transport pass fails; the value is left as Lean's: " ++ CErrors.print e);
      None)
  | Some _ | None -> None
