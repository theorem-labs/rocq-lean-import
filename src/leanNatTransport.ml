(* Transport of SProp arguments across closed Nat terms of equal value (see the .mli and README, "Transport
   of proof arguments across Nat literals"). The values this module computes with OCaml's Z are not trusted:
   they only find the places to transport. Each place gets a lemma [x = y], and the kernel checks it; a wrong
   value gives a lemma the kernel refuses. For two Nat terms the proof goes through Rocq's binary [N] (the
   lemmas after [toN] in src/Lean.v); for the two values of a [Fin] (the Fin case, [fin_hole]) it goes through
   the unary literal of their value ([fin_eq_proof]), with which the kernel converts each of them on the unary
   [Nat], so the value and every operand but a divisor are below [fin_ceiling].

   The pass is optional work: every step of it is charged to a budget before the step or allocation it pays
   for (the charged term layer, LeanChargedTerm), but for one: the export's constants of a Lean name, which the
   importer lists ([consts]), are charged by the length of the list once it is returned, since that length is
   not known before; [setup] asks for 47 fixed names, once per entry. The pass asks Rocq for no unbounded
   reduction or retyping. It reads types and exposes products and sorts by its own charged head reduction
   (unfolding of a transparent constant, beta, zeta, cast, projection of a constructor: LeanChargedTerm's
   [whd]); a type it cannot read that way is no type, and the argument gets no cast. When it stops, Lean's own
   value goes to the kernel, which checks it as without the pass. *)

open Names

module C = LeanChargedTerm

type context = {
  consts : string list -> Constant.t list;
  declare : Id.t -> Constr.types -> Constr.t -> GlobRef.t;
  log : Pp.t -> unit;
}

type transported = { value : Constr.t; count : int; lemmas : Id.t list }

(* The smallest value worth a lemma: the kernel compares smaller ones unit by unit quickly enough. *)
let transport_min = Z.of_int 4096

(* The Fin case covers Fin values below this one: its lemma goes through the unary literal of the value, with
   which the kernel converts each of the two values by computing it ([t % 2 ^ 32], [x &&& y]) on the unary [Nat],
   in time and stack that grow with each number it computes. *)
let fin_ceiling = Z.of_int 65536

(* The parameters and the bounds of two Fin chains that are not the same term are compared by value below this
   one, every operand, a divisor included, too ([param_value]): the kernel converts them on the unary [Nat] in
   the cast (tests/fin_transport_bitwise.v casts at the parameters 1023 and 1024, w_1023 and w_1024, and not at
   1025, w_1025). A number, not a count of bits. *)
let param_ceiling = Z.of_int 1025

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

(* The export's names of one operation: its function, its class function, and Nat's instance of the class
   function as Lean's library builds it; Lean names in a spec, the export's constants of each in a row
   ([resolve_names]). *)
type 'k op_names = { funs : 'k; classes : 'k; inst_pat : 'k pat }

(* One row per operation: its names, the value, Rocq's [N] function and the [toN] lemma of src/Lean.v with its
   arguments after the export's function [g]: the lemma of the operation it is defined from ([prev]) and its
   defining equations, each closed by [Logic.eq_refl] on open terms (as Lean's [Nat.pow_succ := rfl]). *)
type op_spec = {
  op : nat_op;
  names : string list op_names;
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
      names =
        {
          funs = [ "Nat"; "add" ];
          classes = [ "HAdd"; "hAdd" ];
          inst_pat = Inst ([ "instHAdd" ], [ Nat_type; Inst ([ "instAddNat" ], []) ]);
        };
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
      names =
        {
          funs = [ "Nat"; "mul" ];
          classes = [ "HMul"; "hMul" ];
          inst_pat = Inst ([ "instHMul" ], [ Nat_type; Inst ([ "instMulNat" ], []) ]);
        };
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
      names =
        {
          funs = [ "Nat"; "pow" ];
          classes = [ "HPow"; "hPow" ];
          inst_pat =
            Inst
              ( [ "instHPow" ],
                [ Nat_type; Nat_type; Inst ([ "instPowNat" ], [ Nat_type; Inst ([ "instNatPowNat" ], []) ]) ] );
        };
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
type op_row = { spec : op_spec; op_consts : Constant.t list op_names }

(* The Nat operations the Fin case reads besides [%] and the forms of [nat_form]: their names and the value,
   [None] where the value is not computed (a shift left by more than 16 of a first operand that is not 0). Each
   operand is a reader's value, below [fin_ceiling], so each result is below 2 ^ 32 ([shiftLeft] below
   2 ^ 16 * 2 ^ 16) and each shift OCaml's [Z] makes is small; the bound of [shiftLeft] and the cap of
   [shiftRight] at 17 change no value a reader keeps: a positive operand shifted left by 17 or more is at least
   131072, and a value below 2 ^ 16 shifted right by 16 or more is 0. *)
type fin_op_spec = { fin_names : string list op_names; fin_z : Z.t -> Z.t -> Z.t option }

let class_inst inst op_inst = Inst ([ inst ], [ Nat_type; Inst (op_inst, []) ])

(* The names of [%], which the Fin case reads ([mod_operands]). *)
let mod_names =
  { funs = [ "Nat"; "mod" ]; classes = [ "HMod"; "hMod" ]; inst_pat = class_inst "instHMod" [ "Nat"; "instMod" ] }

let fin_op_specs =
  let shift_left a b =
    if Z.equal a Z.zero then Some Z.zero
    else if Z.leq b (Z.of_int 16) then Some (Z.shift_left a (Z.to_int b))
    else None
  in
  let row funs classes inst_pat fin_z = { fin_names = { funs; classes; inst_pat }; fin_z } in
  [
    row [ "Nat"; "land" ] [ "HAnd"; "hAnd" ]
      (class_inst "instHAndOfAndOp" [ "Nat"; "instAndOp" ])
      (fun a b -> Some (Z.logand a b));
    row [ "Nat"; "lor" ] [ "HOr"; "hOr" ] (class_inst "instHOrOfOrOp" [ "Nat"; "instOrOp" ]) (fun a b -> Some (Z.logor a b));
    row [ "Nat"; "xor" ] [ "HXor"; "hXor" ]
      (class_inst "instHXorOfXorOp" [ "Nat"; "instXorOp" ])
      (fun a b -> Some (Z.logxor a b));
    row [ "Nat"; "shiftLeft" ] [ "HShiftLeft"; "hShiftLeft" ]
      (class_inst "instHShiftLeftOfShiftLeft" [ "Nat"; "instShiftLeft" ])
      shift_left;
    row [ "Nat"; "shiftRight" ] [ "HShiftRight"; "hShiftRight" ]
      (class_inst "instHShiftRightOfShiftRight" [ "Nat"; "instShiftRight" ])
      (fun a b -> Some (Z.shift_right a (Z.to_int (Z.min b (Z.of_int 17)))));
    row [ "Nat"; "sub" ] [ "HSub"; "hSub" ] (class_inst "instHSub" [ "instSubNat" ]) (fun a b ->
        Some (Z.max Z.zero (Z.sub a b)));
    row [ "Nat"; "div" ] [ "HDiv"; "hDiv" ] (class_inst "instHDiv" [ "Nat"; "instDiv" ]) (fun a b ->
        Some (if Z.equal b Z.zero then Z.zero else Z.div a b));
  ]

(* A row of [fin_op_specs] at one entry: its constants in the export. *)
type fin_op_row = { fin_spec : fin_op_spec; fin_op_consts : Constant.t list op_names }

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

(* A reader of the Fin case ([fin_read]): the values it keeps are below [ceiling]; the divisor of a [%] is read
   by [value], with no ceiling, when [divisor_by_value] (the Fin values: the kernel compares a divisor and does
   not compute it), else by the reader itself (the parameters); its memo per term and per constant. *)
type reader = {
  ceiling : Z.t;
  divisor_by_value : bool;
  rmemo : Z.t option C.memo;
  rconsts : (Constant.t, Z.t option) C.table;
}

(* The pass at one entry: the budget of its parts and the memos of the charged term layer ([ch]), the entry's
   view of the export, which [setup] reads once, and the memos and results of the pass. *)
type state = {
  ctx : context;
  refs : refs;
  ch : C.t;
  entry : Id.t;
  rows : op_row list;
  of_nat : Constant.t list;
  inst_of_nat : Constant.t list;
  triggers : (Constant.t, unit) C.table;  (** the constants that may make an entry need the pass *)
  mod_op : Constant.t list op_names;  (** the export's [%]: [Nat.mod], [HMod.hMod] and Nat's instance of it *)
  unary_succ : bool;  (** [Nat_succ]'s declared type is one relevant Nat argument to Nat *)
  unary_double : bool;  (** the same for [Nat_double] *)
  mutable lemma_ops : (nat_op * (Constr.t * Constr.t) option) list;  (** [lemma_of], at most one per row *)
  records : (inductive, bool) C.table;  (** [one_field_record], per inductive type *)
  fin_consts : (Constant.t, bool) C.table;  (** [fin_typed_const], per constant *)
  data_records : (inductive, bool) C.table;  (** [data_record], per inductive type *)
  data_consts : (Constant.t, bool) C.table;  (** [data_typed_const], per constant *)
  fin_ops : fin_op_row list;  (** the rows of [fin_op_specs] at this entry *)
  values : Z.t option C.memo;
  const_values : (Constant.t, Z.t option) C.table;
  fin_reader : reader;  (** [fin_value] *)
  param_reader : reader;  (** [param_value] *)
  certs : (Z.t * Constr.t * int) option C.memo;
  const_certs : (Constant.t, (Z.t * Constr.t * int) option) C.table;
  mutable next : int;  (** the number of the next lemma this entry generates *)
  mutable count : int;  (** arguments transported *)
  mutable lemmas : Id.t list;  (** the lemmas they use, last first *)
  lemma_ids : (Id.t, unit) C.table;  (** the same, as a set *)
}

let mem_const st c l =
  List.exists
    (fun c' ->
      C.tick st.ch 1;
      Constant.CanOrd.equal c c')
    l

let is_nat_ind nt c = match Constr.kind c with Constr.Ind (ind, _) -> Ind.CanOrd.equal ind nt.nt_nat | _ -> false

(* Whether [c] is [Nat_succ]. *)
let is_nat_succ nt c =
  match Constr.kind c with Constr.Construct ((ind, 2), _) -> Ind.CanOrd.equal ind nt.nt_nat | _ -> false

(* The patterns are the fixed rows above; a list of constants they name is the export's and is charged in
   [mem_const]. *)
let rec pat_matches st p c =
  match p with
  | Nat_type -> is_nat_ind st.refs c
  | Any -> true
  | Inst (ks, ps) -> (
    let h, args = Constr.decompose_app c in
    let rec all i = function [] -> true | p :: ps -> pat_matches st p args.(i) && all (i + 1) ps in
    match Constr.kind h with
    | Constr.Const (k, _) -> Array.length args = List.length ps && mem_const st k ks && all 0 ps
    | _ -> false)

(* Whether [k] applied to [args] is the operation of [ops]: its function applied to two arguments, or its class
   function at Nat's instance applied to six; each comparison charged. Its operands are the last two arguments. *)
let is_op st ops k args =
  let nt = st.refs in
  match Array.length args with
  | 2 -> mem_const st k ops.funs
  | 6 ->
    mem_const st k ops.classes && is_nat_ind nt args.(0) && is_nat_ind nt args.(1) && is_nat_ind nt args.(2)
    && pat_matches st ops.inst_pat args.(3)
  | _ -> false

(* The one recognizer of the Nat forms: every guard is here. A constant of type Nat unfolds to its value, read
   by the charged body reader of LeanChargedTerm. *)
let nat_form st depth c =
  let nt = st.refs in
  let h, args = Constr.decompose_app c in
  let nargs = Array.length args in
  match Constr.kind h with
  | Constr.Construct ((ind, 1), _) when nargs = 0 && Ind.CanOrd.equal ind nt.nt_nat -> Some Zero
  | Constr.Construct _ when nargs = 1 && is_nat_succ nt h -> Some (Succ args.(0))
  | Constr.Const (k, _) when nargs = 1 && Constant.CanOrd.equal k nt.nt_double -> Some (Double args.(0))
  | Constr.Const (k, u) when nargs = 0 -> (
    match C.const_decl st.ch k with
    | Some cb when is_nat_ind nt cb.Declarations.const_type ->
      Option.map (fun b -> Unfold b) (C.def_body st.ch depth u cb)
    | Some _ | None -> None)
  | Constr.Const (k, _)
    when nargs = 3 && mem_const st k st.of_nat && is_nat_ind nt args.(0)
         && pat_matches st (Inst (st.inst_of_nat, [ Any ])) args.(2) ->
    Some (Unfold (snd (Constr.decompose_app args.(2))).(0))
  | Constr.Const (k, _) when nargs = 6 || nargs = 2 ->
    List.find_map
      (fun row ->
        if is_op st row.op_consts k args then
          let f = if nargs = 6 then Constr.mkApp (h, Array.sub args 0 4) else h in
          Some (Op (row, f, args.(nargs - 2), args.(nargs - 1)))
        else None)
      st.rows
  | _ -> None

(* The memo of [c]: its constant's table when it is a constant without universe instance, which never evicts,
   else its own slot. *)
let memo_find st phys consts c =
  match Constr.kind c with
  | Constr.Const (k, u) when UVars.Instance.is_empty u -> C.table_find st.ch consts k
  | _ -> C.memo_get st.ch phys c

let memo_add st phys consts c v =
  match Constr.kind c with
  | Constr.Const (k, u) when UVars.Instance.is_empty u -> C.table_add st.ch consts k v
  | _ -> C.memo_put st.ch phys c v

(* The term under a run of [Nat_succ] applications, and [j] plus the length of the run: one step each, as
   [compute] charges a node, in a loop. *)
let rec succ_run st c j =
  match Constr.kind c with
  | Constr.App (h, [| x |]) when is_nat_succ st.refs h ->
    C.tick st.ch 1;
    succ_run st x (j + 1)
  | _ -> (c, j)

(* The value of the closed Nat term [c], the nesting checked before the memo is read. A term is computed again
   only when its slot of the memo holds another term; a constant without universe instance is kept in a table,
   which never evicts, so it is computed once per entry. *)
let rec value st depth c =
  C.check_depth depth;
  match memo_find st st.values st.const_values c with
  | Some v -> v
  | None ->
    let v = compute st depth c in
    memo_add st st.values st.const_values c v;
    v

and compute st depth c =
  C.tick st.ch 1;
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
  C.check_depth depth;
  match nat_form st depth c with
  | Some Zero -> true
  | Some (Succ m | Double m) ->
    C.tick st.ch 1;
    is_literal st (depth + 1) m
  | Some (Unfold _ | Op _) | None -> false

(* The literal [c] unfolds to, if it is one: the kernel converts two terms of the same literal without
   arithmetic. *)
let rec literal_of st depth c =
  C.check_depth depth;
  if is_literal st depth c then Some c
  else
    match nat_form st depth c with
    | Some (Unfold b) ->
      C.tick st.ch 1;
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
          C.tick st.ch 1;
          if
            UVars.AbstractContext.is_empty
              (Declareops.constant_polymorphic_context (Environ.lookup_constant c st.ch.C.genv))
          then Some (Constr.mkConstU (c, UVars.Instance.empty))
          else None)
        row.op_consts.funs
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
   literals. A proof built once is used again, its size counted again. The nesting is checked before the memo
   is read. *)
let rec certify st depth t =
  C.check_depth depth;
  match memo_find st st.certs st.const_certs t with
  | Some r ->
    (match r with Some (_, _, size) -> C.tick st.ch size | None -> ());
    r
  | None ->
    let r = certify_node st depth t in
    memo_add st st.certs st.const_certs t r;
    r

and certify_node st depth t =
  let nt = st.refs in
  match value st depth t with
  | None -> None
  | Some v ->
    C.tick st.ch 1;
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
          let hfg = lam2 nt (refl_nat nt (app (C.lift_ch st.ch depth 2 f) [| r2; r1 |])) in
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

(* The line about a generated lemma [id : x = y] the kernel refuses with [e]: the statement only when it is
   small enough to print, and the kernel's error only when the proof is too. *)
let refused_lemma_msg id x y proof e =
  if C.printable [ x; y ] then
    let env = Global.env () in
    let pr = Printer.pr_constr_env env (Evd.from_env env) in
    Pp.(
      str "the generated lemma " ++ Id.print id ++ str " : " ++ pr x ++ str " = " ++ pr y ++ str " is refused by the kernel"
      ++ (if C.printable [ proof ] then str ": " ++ CErrors.print e
          else str " (its proof has more than " ++ int C.print_bound ++ str " nodes: the kernel's error is not printed)"))
  else
    Pp.(
      str "the generated lemma " ++ Id.print id ++ str " is refused by the kernel (its statement has more than "
      ++ int C.print_bound ++ str " nodes and is not printed)")

(* The universe instance of src/Lean.v's [eq] at Nat: that of the lemmas' statements and of their [eq_refl]. *)
let eq_inst = UVars.Instance.of_array ([||], [| Univ.Level.set |])

(* [x = y] at Nat: src/Lean.v's [eq] at [eq_inst]. *)
let eq_nat nt x y = app (Constr.mkIndU (nt.nt_eq, eq_inst)) [| nat_type nt; x; y |]

(* Declare [proof] as the lemma [x = y] (src/Lean.v's [eq] at Nat), named [<entry>__nat_eq_<k>] or, when that
   name is taken, the next free one as [Namegen] counts them (each name it tries charged), and keep it for a
   later place with the same two terms. A lemma the kernel refuses is logged and not used. *)
let declare_nat_eq st x y proof =
  let nt = st.refs in
  let ty = eq_nat nt x y in
  st.next <- st.next + 1;
  let id = Id.of_string (Id.to_string st.entry ^ "__nat_eq_" ^ string_of_int st.next) in
  let taken id =
    C.tick st.ch 1;
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
      C.tick st.ch 1;
      if C.equal st.ch depth x x' && C.equal st.ch depth y y' then Some c else find rest
  in
  find !lemma_cache

(* Whether [x] and [y] are closed and use only declared universes; Rocq's walk of both for their universes is
   paid first. *)
let lemma_terms_ok st depth x y =
  C.closed st.ch depth x && C.closed st.ch depth y
  &&
  (C.pay st.ch (C.add_size (C.size st.ch depth x) (C.size st.ch depth y));
   let levels = Vars.universes_of_constr ~init:(Vars.universes_of_constr x) y in
   Result.is_ok (UGraph.check_declared_universes (Global.universes ()) levels))

(* The lemma [x = y] for two closed Nat terms, at the nesting [depth] of the place that needs it: the file's
   cached one, or one declared on first use with the proof [proof ()]; [None] when the terms do not pass
   [lemma_terms_ok] or [proof ()] is [None]. *)
let eq_lemma st depth x y proof =
  match cached_nat_eq st depth x y with
  | Some c -> Some c
  | None -> (
    if not (lemma_terms_ok st depth x y) then None
    else match proof () with Some p -> declare_nat_eq st x y p | None -> None)

(* The proof of [x = y] for two closed Nat terms of equal value: through Rocq's binary [N]. *)
let nat_eq_proof st depth x y () =
  match (certify st depth x, certify st depth y) with
  | Some (vx, cx, _), Some (vy, cy, _) when Z.equal vx vy ->
    Some (app st.refs.nt_nat_eq [| x; y; n_literal st.refs vx; cx; cy |])
  | _ -> None

(* The unary literal [Nat_succ^v Nat_zero] of [v], a value below [fin_ceiling]: its [v] steps charged before
   its [v] nodes are built. *)
let nat_unary st v =
  let nt = st.refs in
  let n = Z.to_int v in
  C.tick st.ch n;
  let succ = Constr.mkConstructU ((nt.nt_nat, 2), UVars.Instance.empty) in
  let rec go k acc = if k = 0 then acc else go (k - 1) (Constr.mkApp (succ, [| acc |])) in
  go n (nat_zero nt)

(* The proof of [x = y] for the Nat values [x] and [y], of value [v], of the [Fin] at the bottom of two closed
   terms (see [fin_hole]): through the unary literal [l] of [v], [sprop_transport (fun n => x = n) l y
   (eq_refl l) (eq_refl x)], so that the kernel converts each of [x] and [y] with [l] on its own, computing it on
   the unary [Nat]. Two such terms converted with each other ([(224 : UInt8) &&& 128] against [128]) can take
   the kernel's lazy conversion through a far longer path. [x] and [y] are shared, not copied, and [x], closed,
   needs no lift under [n]; the other nodes are a fixed few. *)
let fin_eq_proof st x y v () =
  let nt = st.refs in
  let l = nat_unary st v in
  let refl = Constr.mkConstructU ((nt.nt_eq, 1), eq_inst) in
  Some
    (app nt.nt_transport
       [| lam1 nt (eq_nat nt x r1); l; y; app refl [| nat_type nt; l |]; app refl [| nat_type nt; x |] |])

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
   equal value [fv] ([Fin_hole]). *)
type hole =
  | Nat_hole of Constr.t * Constr.t
  | Fin_hole of { fa : Constr.t; fd : Constr.t; sa : fin_side; sd : fin_side; fv : Z.t }

let hole_terms = function Nat_hole (x, y) -> (x, y) | Fin_hole { fa; fd; _ } -> (fa, fd)

(* Two closed Nat terms of different values: the types cannot be converted, the argument is left as is. *)
exception Other_values

(* The most records of one field [fin_spine] goes through above the [Fin]: zero to four; a fifth gives no hole. *)
let max_spine = 4

(* Whether [ind] has one constructor with one field (after its parameters), and is not mutual. *)
let one_field_record st ind =
  match C.table_find st.ch st.records ind with
  | Some b -> b
  | None ->
    let mib, mip = Inductive.lookup_mind_specif st.ch.C.genv ind in
    let b =
      Array.length mib.Declarations.mind_packets = 1
      && Array.length mip.Declarations.mind_consnames = 1
      && mip.Declarations.mind_consnrealargs.(0) = 1
    in
    C.table_add st.ch st.records ind b;
    b

(* [c] reduced through at most [max_spine] records of one field to a [Fin], [n] records and [steps] reduction
   steps of the side already taken: each head reduction by [C.whd], so at most [C.max_head_steps] steps of the
   side in all (its own, the subject of each projection, and the field of each record). *)
let rec fin_spine st depth n steps c acc =
  C.tick st.ch 1;
  C.check_depth depth;
  if n > max_spine then None
  else
    match C.whd st.ch st.ch.C.genv depth steps c with
    | None -> None
    | Some (steps, h, args) -> (
      match Constr.kind h with
      | Constr.Construct ((ind, 1), _) when Ind.CanOrd.equal ind st.refs.nt_fin && Array.length args = 3 ->
        Some { spine = List.rev acc; fin_mk = h; bound = args.(0); fval = args.(1); fprf = args.(2) }
      | Constr.Construct ((ind, 1), _) when one_field_record st ind && Array.length args >= 1 ->
        let k = Array.length args - 1 in
        fin_spine st (depth + 1) (n + 1) steps args.(k) ((h, C.sub_ch st.ch args 0 k) :: acc)
      | _ -> None)

(* The two operands of [c] when it is a [%] the Fin case reads ([is_op] of the export's [%]). *)
let mod_operands st c =
  let h, args = Constr.decompose_app c in
  let n = Array.length args in
  match Constr.kind h with
  | Constr.Const (k, _) when is_op st st.mod_op k args -> Some (args.(n - 2), args.(n - 1))
  | _ -> None

(* [c] as an operation of a row of [fin_op_specs], with its two operands ([is_op] of each row). *)
let fin_op_app st c =
  let h, args = Constr.decompose_app c in
  let n = Array.length args in
  match Constr.kind h with
  | Constr.Const (k, _) when n = 2 || n = 6 ->
    List.find_map
      (fun row -> if is_op st row.fin_op_consts k args then Some (row, args.(n - 2), args.(n - 1)) else None)
      st.fin_ops
  | _ -> None

(* What a reader of the Fin case reads at the head of [c], without reducing it: a [%] ([mod_operands]), a form
   of [nat_form], or an operation of [fin_op_specs] ([fin_op_app]), tried in that order, each test charged. *)
type fin_form = Mod of Constr.t * Constr.t | Form of nat_form | Bit of fin_op_row * Constr.t * Constr.t

let fin_form st depth c =
  match mod_operands st c with
  | Some (x, y) -> Some (Mod (x, y))
  | None -> (
    match nat_form st depth c with
    | Some f -> Some (Form f)
    | None -> Option.map (fun (row, x, y) -> Bit (row, x, y)) (fin_op_app st c))

(* Whether a reader of the Fin case reads [c] at its head ([fin_form]). *)
let fin_known st depth c = Option.has_some (fin_form st depth c)

(* The value of the closed Nat term [c] for the Fin case by the reader [r]: [st.fin_reader] for the two Fin
   values of [fin_hole] ([fin_value]), [st.param_reader] for the parameters and bounds of their chains
   ([param_value]). It reads a [%] (its dividend by [r], its divisor by [value] or by [r], positive), a form of
   [nat_form] (a literal, a constant of type Nat, [OfNat.ofNat Nat], a run of [Nat_succ], [+], [*], [^], each
   operand by [r]), an operation of [fin_op_specs] (each operand by [r]), and a term it reads none of after a head
   reduction ([C.whd], from a count of 0, at most [C.max_head_steps] steps) to a term it reads: [BitVec.toNat x]
   reads the value of the [Fin] that [x] reduces to. The kernel checks a Fin lemma by computing each side on the
   unary [Nat], in time that grows with each number it computes but a divisor ([Nat.mod n m] compares [m] with
   [n], which stops at [n]); so the value and every operand it reads are below [r.ceiling], the divisor too when
   [r] reads it. [None] otherwise, and at any other end of the head reduction. The nesting is checked before the
   memo is read; a term is computed again only when its slot of the memo holds another term, a constant without
   universe instance once per entry (its table never evicts), and each computation is charged. *)
let rec fin_read st r depth c =
  C.check_depth depth;
  match memo_find st r.rmemo r.rconsts c with
  | Some v -> v
  | None ->
    let v = fin_read_node st r depth c in
    memo_add st r.rmemo r.rconsts c v;
    v

and fin_read_node st r depth c =
  C.tick st.ch 1;
  let below v = if Z.lt v r.ceiling then Some v else None in
  let read = fin_read st r (depth + 1) in
  let both x y f = match (read x, read y) with Some a, Some b -> Option.bind (f a b) below | _ -> None in
  match fin_form st depth c with
  | Some (Mod (x, y)) -> (
    let divisor = if r.divisor_by_value then value st (depth + 1) y else read y in
    match (read x, divisor) with Some a, Some b when Z.sign b > 0 -> below (Z.rem a b) | _ -> None)
  | Some (Form Zero) -> Some Z.zero
  | Some (Form (Unfold b)) -> read b
  | Some (Form (Succ x)) ->
    (* [c] is [Nat_succ] applied [j] times to [b]; its value is the largest of the run *)
    let b, j = succ_run st x 1 in
    Option.bind (read b) (fun v -> below (Z.add v (Z.of_int j)))
  | Some (Form (Double x)) -> Option.bind (read x) (fun v -> below (Z.shift_left v 1))
  | Some (Form (Op (row, _, x, y))) -> both x y row.spec.z
  | Some (Bit (row, x, y)) -> both x y row.fin_spec.fin_z
  | None -> (
    match C.whd ~stop:(fin_known st (depth + 1)) st.ch st.ch.C.genv (depth + 1) 0 c with
    | Some (_, h, args) ->
      let c' = C.app_ch st.ch h args in
      if fin_known st (depth + 1) c' then read c' else None
    | None -> None)

let fin_value st depth c = fin_read st st.fin_reader depth c

let param_value st depth c = fin_read st st.param_reader depth c

let same_constructor c c' =
  match (Constr.kind c, Constr.kind c') with
  | Constr.Construct (k, _), Constr.Construct (k', _) -> Construct.CanOrd.equal k k'
  | _ -> false

let head_const c = match Constr.kind (fst (Constr.decompose_app c)) with Constr.Const (k, _) -> Some k | _ -> None

(* Whether a parameter, or the bound, of the two chains of a Fin pair is the same: the same term, or two closed
   Nat terms ([fin_hole] reads closed sides only) of the same value by [param_value], [y] read only when [x] has
   one. The cast leaves their conversion to the kernel. *)
let same_param st depth x y =
  C.equal st.ch depth x y
  ||
  match param_value st depth x with
  | None -> false
  | Some a -> ( match param_value st depth y with Some b -> Z.equal a b | None -> false)

(* Whether the two sides go through the same records of one field, with the same parameters ([same_param]), to a
   [Fin] of the same bound; each comparison charged. *)
let same_records st depth sa sd =
  List.length sa.spine = List.length sd.spine
  && List.for_all2
       (fun (c, ps) (c', ps') ->
         C.tick st.ch 1;
         same_constructor c c' && Array.length ps = Array.length ps' && Array.for_all2 (same_param st depth) ps ps')
       sa.spine sd.spine
  && same_param st depth sa.bound sd.bound

(* The rule of the Fin case (README, "Transport of proof arguments across Nat literals"): [a] (in the
   argument's type) and [d] (in the expected type) are a [Fin_hole] when both are closed, their head constants
   differ, both reduce (at most [C.max_head_steps] steps each side, all its head reductions together) through
   the same records of one field, with the same parameters, to a [Fin] of the same bound ([same_records]), and
   the two [Fin] values are closed Nat terms of equal value that are not the same term. [d]'s side is reduced
   only once [a]'s has reached its [Fin], and its value read only once [a]'s has one. [None] in every other
   case, two different values included: the kernel converts the two terms, or refuses the argument, as without
   the pass, and the pass looks inside them as before. Closedness and every comparison are charged. *)
let fin_hole st depth a d =
  match (head_const a, head_const d) with
  | Some ka, Some kd when (not (Constant.CanOrd.equal ka kd)) && C.closed st.ch depth a && C.closed st.ch depth d -> (
    match fin_spine st depth 0 0 a [] with
    | None -> None
    | Some sa -> (
      match fin_spine st depth 0 0 d [] with
      | Some sd when same_records st depth sa sd -> (
        match fin_value st depth sa.fval with
        | None -> None
        | Some va -> (
          match fin_value st depth sd.fval with
          | Some vd when Z.equal va vd && not (C.equal st.ch depth sa.fval sd.fval) ->
            Some (Fin_hole { fa = a; fd = d; sa; sd; fv = va })
          | Some _ | None -> None))
      | Some _ | None -> None))
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
        C.tick st.ch 1;
        let x', y' = hole_terms h' in
        if C.equal st.ch depth x x' && C.equal st.ch depth y y' then Some k else find rest
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
      else if Z.lt va transport_min || C.equal st.ch depth a d then Some Keep
      else
        match (literal_of st depth a, literal_of st depth d) with
        | Some la, Some ld when C.equal st.ch depth la ld -> Some Keep
        | _ -> Some (add depth (Nat_hole (a, d)))
  in
  let rec go depth a d =
    C.tick st.ch 1;
    C.check_depth depth;
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
            C.tick st.ch (Array.length aa);
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
  C.tick st.ch 1;
  match (shape, Constr.kind d) with
  | Keep, _ -> d
  | Hole k, _ -> hole k depth
  | App_s (sh, sargs), _ ->
    let h, args = Constr.decompose_app d in
    C.tick st.ch (Array.length args);
    C.app_ch st.ch (nat_fill st sh h depth hole) (Array.map2 (fun s c -> nat_fill st s c depth hole) sargs args)
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
    C.tick st.ch 1;
    C.check_depth depth;
    match value st depth c with
    | Some v -> if Z.geq v transport_min then raise_notrace Found
    | None -> Constr.iter (scan (depth + 1)) c
  in
  try
    scan depth c;
    false
  with Found -> true

(* Whether the constant [k]'s declared type ends in an inductive type [accepts] holds of: its declaration read
   directly, each product it goes through charged, the answer kept per constant in [table]. *)
let typed_const st table accepts k =
  match C.table_find st.ch table k with
  | Some b -> b
  | None ->
    let rec concl depth ty =
      C.tick st.ch 1;
      C.check_depth depth;
      match Constr.kind ty with
      | Constr.Prod (_, _, b) | Constr.Cast (b, _, _) -> concl (depth + 1) b
      | _ -> (
        match Constr.kind (fst (Constr.decompose_app ty)) with
        | Constr.Ind (ind, _) -> accepts st ind
        | _ -> false)
    in
    let b = match C.const_decl st.ch k with Some cb -> concl 0 cb.Declarations.const_type | None -> false in
    C.table_add st.ch table k b;
    b

(* Whether the constant [k]'s declared type ends in a record of one field ([UInt32], [BitVec w]). *)
let fin_typed_const st k = typed_const st st.fin_consts one_field_record k

(* Whether [ind] is a data record: a record of one field ([one_field_record]) whose field is relevant and of an
   inductive type ([UInt8] over [BitVec 8], [BitVec w] over [Fin (2 ^ w)]); not a class such as [OfNat α n]
   (its field is of a variable's type) or [NeZero n] (a proposition). Its declaration read on a miss, one step;
   the field's type is read at its head, which an application holds without a copy. *)
let data_record st ind =
  match C.table_find st.ch st.data_records ind with
  | Some b -> b
  | None ->
    let b =
      one_field_record st ind
      &&
      (C.tick st.ch 1;
       let _, mip = Inductive.lookup_mind_specif st.ch.C.genv ind in
       match fst mip.Declarations.mind_nf_lc.(0) with
       | field :: _ ->
         Sorts.relevance_equal (Context.Rel.Declaration.get_relevance field) Sorts.Relevant
         && Constr.isInd (fst (Constr.decompose_app (Context.Rel.Declaration.get_type field)))
       | [] -> false)
    in
    C.table_add st.ch st.data_records ind b;
    b

(* Whether the constant [k]'s declared type ends in a [data_record]. *)
let data_typed_const st k = typed_const st st.data_consts data_record k

(* Whether [args], the arguments of the export's [OfNat.ofNat], are three, the first headed by an inductive type
   [accepts] holds of: [OfNat.ofNat T n i] at such a [T]. *)
let ofnat_at st accepts args =
  Array.length args = 3
  && match Constr.kind (fst (Constr.decompose_app args.(0))) with Constr.Ind (ind, _) -> accepts st ind | _ -> false

(* The gate of the Fin case: whether [c], at the nesting [depth], has a closed application of a constant whose
   type ends in a record of one field, or [OfNat.ofNat] at such a record. The Nat case keeps [has_big_nat]. *)
let has_fin_site st depth c =
  let rec scan depth c =
    C.tick st.ch 1;
    C.check_depth depth;
    (match Constr.kind c with
    | Constr.App (h, args) -> (
      match Constr.kind h with
      | Constr.Const (k, _) ->
        let site = if mem_const st k st.of_nat then ofnat_at st one_field_record args else fin_typed_const st k in
        if site && C.closed st.ch depth c then raise_notrace Found
      | _ -> ())
    | _ -> ());
    Constr.iter (scan (depth + 1)) c
  in
  try
    scan depth c;
    false
  with Found -> true

let is_irrelevant_binder na =
  match Context.binder_relevance na with Sorts.Irrelevant -> true | Sorts.Relevant | Sorts.RelevanceVar _ -> false

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
  match Option.bind (C.ctor_type st.ch depth (ind, i) u) field with
  | Some t -> C.subst_walk st.ch depth [| side.bound; z |] 0 2 t
  | None -> invalid_arg "fin_proof_type"

(* Record the lemma [id] an argument uses, once, in the order of first use. *)
let add_lemma_id st id =
  if Option.is_empty (C.table_find st.ch st.lemma_ids id) then begin
    C.table_add st.ch st.lemma_ids id ();
    st.lemmas <- id :: st.lemmas
  end

(* [arg], whose expected type is the SProp type [dom], at the nesting [depth], cast along the lemmas of its
   holes, or [None] when its type differs from [dom] at no hole. *)
let rec transport_arg st env depth arg dom =
  (* Each argument it looks at has a budget of its own, which [C.Out_of_budget] ends like the entry's; its steps
     count toward the entry's total too. An exception ends the pass, which then reads no budget. *)
  let entry_steps = st.ch.C.steps in
  st.ch.C.steps <- budget ();
  let r = transport_arg_in st env depth arg dom in
  st.ch.C.steps <- entry_steps;
  r

and transport_arg_in st env depth arg dom =
  let dom = C.beta st.ch depth dom in
  if not (has_big_nat st depth dom || has_fin_site st depth dom) then None
  else
    match Option.map (fun ty -> nat_diff st depth (C.beta st.ch depth ty) dom) (C.type_of st.ch env depth arg) with
    | exception Other_values -> None
    | None | Some (_, [||]) -> None
    | Some (shape, holes) ->
      let lemmas =
        Array.map
          (function
            | Nat_hole (x, y) -> eq_lemma st depth x y (nat_eq_proof st depth x y)
            | Fin_hole { sa; sd; fv; _ } -> eq_lemma st depth sa.fval sd.fval (fin_eq_proof st sa.fval sd.fval fv))
          holes
      in
      if Array.exists Option.is_empty lemmas then None
      else begin
        let nt = st.refs in
        (* [dom] under the motive's one or two binders, lifted once each for all the holes. *)
        let dom1 = lazy (C.lift_ch st.ch depth 1 dom) and dom2 = lazy (C.lift_ch st.ch depth 2 dom) in
        let side k j = if j < k then snd (hole_terms holes.(j)) else fst (hole_terms holes.(j)) in
        let cast p k hole =
          C.tick st.ch 1;
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
                  C.tick st.ch (Array.length params + 1);
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
            let lam = Constr.mkLambda (hz, fin_proof_type st depth sd sa.fval, C.lift_ch st.ch depth 1 p) in
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
  && ((st.unary_succ && is_nat_succ st.refs f)
     || st.unary_double
        && match Constr.kind f with Constr.Const (k, _) -> Constant.CanOrd.equal k st.refs.nt_double | _ -> false)

(* [args], the arguments of [f] at the nesting [depth], each SProp argument transported where it needs it.
   [f]'s type is read by [C.type_of]; each product it goes through is charged, and the arguments before it are
   substituted into a domain only for an SProp binder, and into the rest where a product must be exposed. *)
let transport_args st env depth f args =
  let n = Array.length args in
  let out = ref args in
  let set k a =
    if !out == args then begin
      C.tick st.ch n;
      out := Array.copy args
    end;
    !out.(k) <- a
  in
  (* [ty] is the type of [f] applied to the arguments before [k], under the binders that take [!out.(lo)] to
     [!out.(k - 1)]. *)
  let rec loop k lo ty =
    if k < n then begin
      C.tick st.ch 1;
      match Constr.kind ty with
      | Constr.Prod (na, dom, codom) ->
        if is_irrelevant_binder na then
          Option.iter (set k) (transport_arg st env depth !out.(k) (C.subst_walk st.ch depth !out lo (k - lo) dom));
        loop (k + 1) lo codom
      | _ -> (
        match C.expose_prod st.ch env depth (C.subst_walk st.ch depth !out lo (k - lo) ty) with
        | Some ty -> loop k k ty
        | None -> ())
    end
  in
  Option.iter (fun ty -> loop 0 0 ty) (C.type_of st.ch env depth f);
  !out

let rec transport_walk st env depth c =
  C.tick st.ch 1;
  C.check_depth depth;
  let walk env = transport_walk st env (depth + 1) in
  let push d = Environ.push_rel d env in
  match Constr.kind c with
  | Constr.App (f, args) ->
    let f' = walk env f in
    let args' = C.smart_map_ch st.ch (walk env) args in
    let args' = if unary_nat_head st f' args' then args' else transport_args st env depth f' args' in
    if f' == f && args' == args then c else C.app_ch st.ch f' args'
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
  C.tick st.ch 1;
  C.check_depth depth;
  match (Constr.kind body, Constr.kind ty) with
  | Constr.Lambda (na, t, b), Constr.Prod (_, _, tb) ->
    let env = Environ.push_rel (Context.Rel.Declaration.LocalAssum (na, t)) env in
    let b' = transport_result st env (depth + 1) b tb in
    if b' == b then body else Constr.mkLambda (na, t, b')
  | _ ->
    let irrelevant =
      (has_big_nat st depth ty || has_fin_site st depth ty)
      &&
      match C.type_relevance st.ch env depth ty with
      | Some r -> Sorts.relevance_equal Sorts.Irrelevant r
      | None -> false
    in
    if irrelevant then Option.default body (transport_arg st env depth body ty) else body

(* The declared type of a global as its declaration holds it (no instance: the scan below looks for constants
   only). *)
let global_type st g =
  C.tick st.ch 1;
  match g with
  | GlobRef.ConstRef k ->
    Option.map (fun cb -> cb.Declarations.const_type) (Environ.lookup_constant_opt k st.ch.C.genv)
  | GlobRef.IndRef ind ->
    let _, mip = Inductive.lookup_mind_specif st.ch.C.genv ind in
    Some mip.Declarations.mind_user_arity
  | GlobRef.ConstructRef (ind, i) ->
    let _, mip = Inductive.lookup_mind_specif st.ch.C.genv ind in
    Some mip.Declarations.mind_user_lc.(i - 1)
  | GlobRef.VarRef _ -> None

(* Whether the entry may need the pass: [ty], [body] or the type of a global they name holds one of the
   triggers (the rows' constants, [Nat_double], which every literal from 5000 on holds) or a constant of
   type Nat of value [transport_min] or more (its declared type read first, so that only a constant of type
   Nat looks up its value); or [ty] or [body] themselves, not the types of the globals they name, hold
   [OfNat.ofNat T n i] or a constant whose declared type ends in [T], for [T] a [data_record] (the Fin case:
   [(224 : UInt8) &&& 128], [b : UInt8]). *)
let may_apply st ty body =
  let big_const depth k c =
    match C.const_decl st.ch k with
    | Some cb when is_nat_ind st.refs cb.Declarations.const_type -> (
      match value st depth c with Some v -> Z.geq v transport_min | None -> false)
    | Some _ | None -> false
  in
  (* [h] applied to [args] is [OfNat.ofNat T n i] with [T] headed by a data record. *)
  let data_ofnat h args =
    match Constr.kind h with Constr.Const (k, _) -> mem_const st k st.of_nat && ofnat_at st data_record args | _ -> false
  in
  let seen = C.globref_table () in
  let rec scan types depth c =
    C.tick st.ch 1;
    C.check_depth depth;
    match Constr.kind c with
    | Constr.Const (k, _) ->
      if Option.has_some (C.table_find st.ch st.triggers k) || big_const depth k c || (types && data_typed_const st k)
      then raise_notrace Found;
      if types then global depth (GlobRef.ConstRef k)
    | Constr.Ind (ind, _) -> if types then global depth (GlobRef.IndRef ind)
    | Constr.Construct (cs, _) -> if types then global depth (GlobRef.ConstructRef cs)
    | Constr.App (h, args) when types && data_ofnat h args -> raise_notrace Found
    | _ -> Constr.iter (scan types (depth + 1)) c
  and global depth g =
    if Option.is_empty (C.table_find st.ch seen g) then begin
      C.table_add st.ch seen g ();
      Option.iter (scan false (depth + 1)) (global_type st g)
    end
  in
  try
    scan true 0 ty;
    scan true 0 body;
    false
  with Found -> true

(* The export's constants of the Lean name [path]: one step for the call and one per constant of the list the
   importer returns, charged once it is returned (its length is not known before). [setup] asks for 47 fixed
   names, once per entry; the importer builds each list from the instances it declared of that one name. *)
let consts ctx ch path =
  let l = ctx.consts path in
  C.tick ch (1 + List.length l);
  l

let rec resolve ctx ch = function
  | Nat_type -> Nat_type
  | Any -> Any
  | Inst (path, ps) ->
    C.tick ch 1;
    Inst (consts ctx ch path, List.map (resolve ctx ch) ps)

(* The export's constants of each name of an operation. *)
let resolve_names ctx ch names =
  { funs = consts ctx ch names.funs; classes = consts ctx ch names.classes; inst_pat = resolve ctx ch names.inst_pat }

(* Whether [ty] is one relevant Nat argument to Nat. *)
let one_relevant_nat nt ty =
  match Constr.kind ty with
  | Constr.Prod (na, d, c) -> (not (is_irrelevant_binder na)) && is_nat_ind nt d && is_nat_ind nt c
  | _ -> false

(* The pass at the entry [entry]: the entry's view of the export, read once and charged as the rest of its part
   (the rows' constants, the constants of the Fin case and its rows, and the declared types of [Nat_succ] and
   [Nat_double], see [unary_nat_head]), and empty memos. *)
let setup ctx refs ch entry =
  let rows = List.map (fun spec -> { spec; op_consts = resolve_names ctx ch spec.names }) op_specs in
  let fin_ops =
    List.map (fun fin_spec -> { fin_spec; fin_op_consts = resolve_names ctx ch fin_spec.fin_names }) fin_op_specs
  in
  let of_nat = consts ctx ch [ "OfNat"; "ofNat" ] in
  let inst_of_nat = consts ctx ch [ "instOfNatNat" ] in
  let triggers = C.canonical_constant_table () in
  List.iter
    (fun k -> C.table_add ch triggers k ())
    (refs.nt_double :: List.concat_map (fun row -> row.op_consts.funs @ row.op_consts.classes) rows);
  let mod_op = resolve_names ctx ch mod_names in
  let unary_succ =
    match C.ctor_type ch 0 (refs.nt_nat, 2) UVars.Instance.empty with
    | Some ty -> one_relevant_nat refs ty
    | None -> false
  in
  let unary_double =
    match C.const_type ch 0 refs.nt_double UVars.Instance.empty with
    | Some ty -> one_relevant_nat refs ty
    | None -> false
  in
  {
    ctx;
    refs;
    ch;
    entry;
    rows;
    of_nat;
    inst_of_nat;
    triggers;
    mod_op;
    unary_succ;
    unary_double;
    lemma_ops = [];
    records = C.ind_table ();
    fin_consts = C.constant_table ();
    data_records = C.ind_table ();
    data_consts = C.constant_table ();
    fin_ops;
    values = C.memo ();
    const_values = C.constant_table ();
    fin_reader = { ceiling = fin_ceiling; divisor_by_value = true; rmemo = C.memo (); rconsts = C.constant_table () };
    param_reader =
      { ceiling = param_ceiling; divisor_by_value = false; rmemo = C.memo (); rconsts = C.constant_table () };
    certs = C.memo ();
    const_certs = C.constant_table ();
    next = 0;
    count = 0;
    lemmas = [];
    lemma_ids = C.id_table ();
  }

(* The registrations of the rows' [N] functions and [toN] lemmas. *)
let rows_registered () =
  List.for_all (fun spec -> Rocqlib.has_ref spec.n_fun && Rocqlib.has_ref spec.to_n_lemma) op_specs

let transport ctx env ~entry ty body =
  match refs () with
  | Some refs when rows_registered () -> (
    let ch = C.create env ~steps:(budget ()) ~total:(total_budget ()) in
    match
      let st = setup ctx refs ch entry in
      if not (may_apply st ty body) then None
      else
        let body' = transport_result st env 0 (transport_walk st env 0 body) ty in
        (* The list of lemmas has one element per charged insertion of [add_lemma_id]. *)
        if st.count = 0 then None else Some { value = body'; count = st.count; lemmas = List.rev st.lemmas }
    with
    | r -> r
    | exception C.Out_of_budget ->
      ctx.log
        Pp.(
          str "the transport pass stops: it needs more than " ++ int (budget ()) ++ str " steps or a nesting deeper than "
          ++ int C.max_depth ++ str "; the value is left as Lean's");
      None
    | exception C.Out_of_total ->
      ctx.log
        Pp.(
          str "the transport pass stops: it needs more than " ++ int (total_budget ())
          ++ str " steps in total; the value is left as Lean's");
      None
    | exception e when CErrors.noncritical e ->
      (* A fixed text and the exception's name: the error itself may hold terms of any size. *)
      ctx.log
        Pp.(str "the transport pass fails (" ++ str (Printexc.exn_slot_name e) ++ str "); the value is left as Lean's");
      None)
  | Some _ | None -> None
