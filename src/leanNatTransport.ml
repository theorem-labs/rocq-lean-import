(* Transport of SProp arguments across closed Nat terms of equal value (see the .mli and README, "Transport
   of proof arguments across Nat literals"). The values this module computes with OCaml's Z are not trusted:
   they only find the places to transport. Each place gets a lemma [x = y], and the kernel checks it; a wrong
   value gives a lemma the kernel refuses, which leaves its whole argument to Lean's term. For two Nat terms
   the proof goes through Rocq's binary [N] (the lemmas after [toN] in src/Lean.v); for the two values of a
   [Fin] (the Fin case, [fin_hole]) it goes through the unary literal of their value ([fin_eq_proof]), with
   which the kernel converts each of them on the unary [Nat], so the value and every operand but a divisor are
   below [fin_ceiling]; for two closed terms of a data type with different heads (literal arithmetic,
   [ec_hole]) it is the evaluation of both sides in rounds, each Nat operation of [hold_min] or more held and
   given its value by a lemma of its own ([ec_eq_proof]), the lemma [a = d] stated at their type.

   The pass is optional work: every step of it is charged to a budget before the step or allocation it pays
   for (the charged term layer, LeanChargedTerm), but for one: the export's constants of a Lean name, which the
   importer lists ([consts]), are charged by the length of the list once it is returned, since that length is
   not known before; [setup] asks for 47 fixed names, once per entry, and 56 when literal arithmetic's lemmas
   are registered ([l_refs]). The pass asks Rocq for no unbounded reduction or retyping. It reads types and
   exposes products and sorts by its own charged head reduction (unfolding of a transparent constant, beta,
   zeta, cast, projection of a constructor: LeanChargedTerm's [whd]); a type it cannot read that way is no
   type, and the argument gets no cast. When it stops, Lean's own value goes to the kernel, which checks it as
   without the pass. *)

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

(* An integer option of the name [key] that refuses 0 and the negative values ("<key> must be a positive number of
   <unit>, not N."), held in [r] ([None] when unset); the importer declares Lean Entry Timeout and Lean Entry Memory
   Limit by it too. *)
let declare_positive_int_option ~key ~unit r =
  Goptions.declare_int_option
    {
      optdepr = None;
      optstage = Interp;
      optkey = key;
      optread = (fun () -> !r);
      optwrite =
        (fun x ->
          (match x with
          | Some n when n <= 0 ->
            CErrors.user_err
              Pp.(
                str (String.concat " " key) ++ str " must be a positive number of " ++ str unit ++ str ", not " ++ int n
                ++ str ".")
          | None | Some _ -> ());
          r := x);
    }

(* The budget charges the work of one part of an entry: the entry's own scans and walks are one part, and each
   argument the pass looks at is another. A reused certificate costs its full number of steps again: the kernel
   checks the expanded proof tree. All the parts of one entry together get [total_factor] times the budget.
   [Set Lean Transport Step Budget N.] sets it (README, "Lean Transport Step Budget"). *)
let default_budget = 1_000_000

let total_factor = 10

let budget_option = ref None

let () = declare_positive_int_option ~key:[ "Lean"; "Transport"; "Step"; "Budget" ] ~unit:"steps" budget_option

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

(* The instance of one universe [l]: src/Lean.v's [eq@{l}], and [sprop_transport_any@{l}] of literal arithmetic. *)
let inst1 l = UVars.Instance.of_array ([||], [| l |])

(* The universe instance of src/Lean.v's [eq] at Nat: that of the lemmas' statements and of their [eq_refl]. *)
let eq_inst = inst1 Univ.Level.set

(* What literal arithmetic ([ec_hole]) uses from src/Lean.v and Corelib, read apart from [refs ()]: [None] when
   one of them is not registered (a src/Lean.v without its lemmas), and then only literal arithmetic is off: the
   Nat and Fin cases run as without it. The [N] function and the [toN] lemma of its [Sub] row ([lean.N.sub],
   [lean.toN_sub]) are checked here and read by name where a certificate uses them, as the other rows' are. *)
type l_refs = {
  lr_transport_any : Constant.t;  (** [sprop_transport_any@{u}]: the cast at a type of any universe *)
  lr_nat_le : inductive;  (** src/Lean.v's [Nat_le], Lean's [Nat.le] predeclared *)
  lr_le_of_toN : Constr.t;
  lr_of_eq : Constr.t;
  lr_pred : Constr.t;  (** [toN_pred] *)
  lr_bool : Constr.t;  (** Corelib's [bool], of the [N.leb] checks *)
  lr_true : Constr.t;
}

(* [sprop_transport_any] at the universe [l]. *)
let transport_any lr l = Constr.mkConstU (lr.lr_transport_any, inst1 l)

let nat_type nt = Constr.mkIndU (nt.nt_nat, UVars.Instance.empty)
let nat_zero nt = Constr.mkConstructU ((nt.nt_nat, 1), UVars.Instance.empty)
let nat_succ nt t = Constr.mkApp (Constr.mkConstructU ((nt.nt_nat, 2), UVars.Instance.empty), [| t |])
let refl_nat nt t = Constr.mkApp (nt.nt_refl, [| nat_type nt; t |])
let refl_n nt w = Constr.mkApp (nt.nt_refl, [| nt.nt_n; w |])
let lam1 nt body = Constr.mkLambda (Context.nameR (Id.of_string "n"), nat_type nt, body)

(* [x = y] at Nat: src/Lean.v's [eq] at [eq_inst]. *)
let eq_nat nt x y = Constr.mkApp (Constr.mkIndU (nt.nt_eq, eq_inst), [| nat_type nt; x; y |])

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

(* The nodes of [n_literal nt v]: one for [N0]; else two for [Npos]'s application, one for [xH] and two for each bit
   below the highest. *)
let n_literal_nodes v = if Z.equal v Z.zero then 1 else (2 * Z.numbits v) + 1

(* Lean's [a / b] ([a / 0] is 0) and [a - b] (truncated at 0). *)
let nat_div a b = if Z.equal b Z.zero then Z.zero else Z.div a b

let nat_sub a b = Z.max Z.zero (Z.sub a b)

(* The importer's literals (lean.ml's [nat_int]): below [max_nat_int] [Nat_succ] applied [v] times to [Nat_zero];
   from it on [large_literal], [Nat_succ] applied [r] times to the binary form of [v - r] built with [Nat_double],
   [r] in 1..[lit_segment] chosen so that [v - r] is congruent to [lit_segment / 2] modulo [lit_segment]. In each
   block [b + 1] through [b + lit_segment], large literals use the same binary form of [b]. If [j] and [j - 1] are
   large literals in the same block, the predecessor of the literal [j] is the literal [j - 1], term for term. At
   the lower boundary the predecessor of the literal [b + 1] is the binary form of [b], not the literal [b].

   This matters to the kernel's conversion. Matching a literal against [Nat_succ] yields its predecessor; when that
   is a closed term, two of them are compared structurally ([fast_test]). When it comes from reducing [Nat_double],
   it is a closure of [double]'s fixpoint, and two such closures are compared one [Nat_succ] at a time, each a
   non-tail call: the depth is the value. When conversion strips [k] successors off the literal [j] and meets the
   literal [j - k] in the same block ([k < r]), the two terms match structurally. Crossing the block boundary can
   still force a unary walk: [Nat.pred] of the literal 134217733 reaches the bare binary form of 134217732, not the
   literal 134217732.

   [lit_segment] is small because the cost of some conversions grows quickly with the number [r] of leading
   [Nat_succ]: importing dumps/lean434/linear.ndjson (fixedVar = 100000000) takes 3.7 s with [r] = 8 and 10.9 s with
   [r] = 16, and one entry runs past 60 s with [r] = 32 or with the plain binary form. The evaluation of literal
   arithmetic writes the literals it computes in this form too ([nat_lit]), so that the kernel compares them term
   for term with the importer's. *)
let max_nat_int = Z.of_int 5000

let lit_segment = 8

(* The [r] of [v]: its leading [Nat_succ] applications. *)
let lit_succs v = 1 + Z.to_int (Z.rem (Z.sub (Z.pred v) (Z.of_int (lit_segment / 2))) (Z.of_int lit_segment))

let large_literal nat double v =
  let zero = Constr.mkConstructU ((nat, 1), UVars.Instance.empty) in
  let succ = Constr.mkConstructU ((nat, 2), UVars.Instance.empty) in
  let rec bin z =
    if Z.equal z Z.zero then zero
    else
      let d = Constr.mkApp (double, [| bin (Z.shift_right z 1) |]) in
      if Z.testbit z 0 then Constr.mkApp (succ, [| d |]) else d
  in
  let rec succs k c = if k = 0 then c else succs (k - 1) (Constr.mkApp (succ, [| c |])) in
  let r = lit_succs v in
  succs r (bin (Z.sub v (Z.of_int r)))

let bounded v = if Z.numbits v <= max_bits then Some v else None

let z_pow b e =
  if Z.gt e (Z.of_int max_bits) then None
  else if Z.leq b Z.one then Some (if Z.equal e Z.zero then Z.one else b)
  else if Z.numbits b * Z.to_int e > 2 * max_bits then None
  else bounded (Z.pow b (Z.to_int e))

(* The shape of a term, the constants named by their Lean names: Lean's [Nat], any term, or one of the
   constants applied to arguments of those shapes. *)
type 'k pat = Nat_type | Any | Inst of 'k * 'k pat list

type nat_op = Add | Mul | Pow | Sub

(* The export's names of one operation: its function, its class function, and Nat's instance of the class
   function as Lean's library builds it; Lean names in a spec, the export's constants of each in a row
   ([resolve_names]). *)
type 'k op_names = { funs : 'k; classes : 'k; inst_pat : 'k pat }

(* One row per operation: its names, the value, Rocq's [N] function and the [toN] lemma of src/Lean.v with its
   arguments after the export's function [g]: the lemma of the operation it is defined from ([prev]), for [Sub]
   the export's [Nat.pred] with its lemma [toN_pred] ([pred], literal arithmetic's [lstate]), and its defining
   equations, each closed by [Logic.eq_refl] on open terms (as Lean's [Nat.pow_succ := rfl]). *)
type op_spec = {
  op : nat_op;
  names : string list op_names;
  z : Z.t -> Z.t -> Z.t option;
  n_fun : string;
  to_n_lemma : string;
  prev : nat_op option;
  lemma_args :
    refs -> prev:(Constr.t * Constr.t) option -> pred:(Constr.t * Constr.t) option -> Constr.t -> Constr.t array option;
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
        (fun nt ~prev:_ ~pred:_ add ->
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
        (fun nt ~prev ~pred:_ mul ->
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
        (fun nt ~prev ~pred:_ pow ->
          (* pow b 0 = 1, pow b (S e) = mul (pow b e) b *)
          Option.map
            (fun (mul, hmul) ->
              [| mul; pow; hmul; lam1 nt (refl_nat nt (nat_succ nt (nat_zero nt)));
                 lam2 nt (refl_nat nt (app mul [| app pow [| r2; r1 |]; r2 |])) |])
            prev);
    };
  ]

let class_inst inst op_inst = Inst ([ inst ], [ Nat_type; Inst (op_inst, []) ])

(* The names of Lean's [-] and [/]: rows of the Fin case ([fin_op_specs]) and of the evaluator's reader of literal
   arithmetic (the [Sub] row and the [Div] form), which read the same constants ([setup_l] finds the rows of these
   very names). *)
let sub_names = { funs = [ "Nat"; "sub" ]; classes = [ "HSub"; "hSub" ]; inst_pat = class_inst "instHSub" [ "instSubNat" ] }

let div_names =
  { funs = [ "Nat"; "div" ]; classes = [ "HDiv"; "hDiv" ]; inst_pat = class_inst "instHDiv" [ "Nat"; "instDiv" ] }

(* The row that only the evaluator's reader of literal arithmetic reads ([ev_op_specs]): Lean's [-], whose lemma
   needs the export's [Nat.pred] with its lemma [toN_pred] besides its defining equations. *)
let sub_spec =
  {
    op = Sub;
    names = sub_names;
    z = (fun a b -> Some (nat_sub a b));
    n_fun = "lean.N.sub";
    to_n_lemma = "lean.toN_sub";
    prev = None;
    lemma_args =
      (fun nt ~prev:_ ~pred sub ->
        (* pred 0 = 0, pred (S n) = n; sub n 0 = n, sub n (S m) = pred (sub n m) *)
        Option.map
          (fun (pred, hpred) ->
            [| pred; hpred; sub; lam1 nt (refl_nat nt r1);
               lam2 nt (refl_nat nt (app pred [| app sub [| r2; r1 |] |])) |])
          pred);
  }

let ev_op_specs = [ sub_spec ]

(* Whether src/Lean.v registers the [N] function and the [toN] lemma of each row. *)
let registered specs = List.for_all (fun spec -> Rocqlib.has_ref spec.n_fun && Rocqlib.has_ref spec.to_n_lemma) specs

let l_refs () =
  try
    match (lib_ref "lean.sprop_transport_any", lib_ref "lean.Nat_le") with
    | GlobRef.ConstRef lr_transport_any, GlobRef.IndRef lr_nat_le when registered ev_op_specs ->
      Some
        {
          lr_transport_any;
          lr_nat_le;
          lr_le_of_toN = lib_term "lean.Nat_le_of_toN";
          lr_of_eq = lib_term "lean.toN_of_eq";
          lr_pred = lib_term "lean.toN_pred";
          lr_bool = lib_term "core.bool.type";
          lr_true = lib_term "core.bool.true";
        }
    | _ -> None
  with Not_found -> None

(* A row at one entry: its constants in the export. *)
type op_row = { spec : op_spec; op_consts : Constant.t list op_names }

(* The Nat operations the Fin case reads besides [%] and the forms of [nat_form]: their names and the value,
   [None] where the value is not computed (a shift left by more than 16 of a first operand that is not 0). Each
   operand is a reader's value, below [fin_ceiling], so each result is below 2 ^ 32 ([shiftLeft] below
   2 ^ 16 * 2 ^ 16) and each shift OCaml's [Z] makes is small; the bound of [shiftLeft] and the cap of
   [shiftRight] at 17 change no value a reader keeps: a positive operand shifted left by 17 or more is at least
   131072, and a value below 2 ^ 16 shifted right by 16 or more is 0. *)
type fin_op_spec = { fin_names : string list op_names; fin_z : Z.t -> Z.t -> Z.t option }

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
    { fin_names = sub_names; fin_z = (fun a b -> Some (nat_sub a b)) };
    { fin_names = div_names; fin_z = (fun a b -> Some (nat_div a b)) };
  ]

(* A row of [fin_op_specs] at one entry: its constants in the export. *)
type fin_op_row = { fin_spec : fin_op_spec; fin_op_consts : Constant.t list op_names }

(* Lean's [/] at one entry, which a reader of literal arithmetic reads as the form [Div]: its constants (the Fin
   case's [div] row's), Lean's [Nat.div_eq_of_lt_le] and literal arithmetic's references, which its certificate
   uses ([certify_div]). *)
type div_reader = { div_op : Constant.t list op_names; div_thms : Constant.t list; div_lr : l_refs }

(* The forms of a closed Nat term: a literal of the importer's form ([Zero], [Succ], [Double], see
   [large_literal]), a term that unfolds to another ([Unfold]: a constant of type Nat, or
   [OfNat.ofNat Nat n (instOfNatNat m)] to [m]), an operation of a row as the term applies it ([Op (row, h, args)]:
   the export's function [h] applied to two operands, or the class function [h] applied to its Nat instance's
   arguments and two operands, the operands last), and, for a reader of Lean's [/] only, a division
   ([Div (dv, args)], the same two shapes), certified through Lean's [Nat.div_eq_of_lt_le]. No reader reads [%] as a
   form ([mod_operands] is the Fin case's own). *)
type nat_form =
  | Zero
  | Succ of Constr.t
  | Double of Constr.t
  | Unfold of Constr.t
  | Op of op_row * Constr.t * Constr.t array
  | Div of div_reader * Constr.t array

(* The two operands of an operation's arguments (the last two), and its form [f], [f a b] the operation: the
   function, or the class function applied to its type arguments and instance (built uncharged). *)
let operands args =
  let n = Array.length args in
  (args.(n - 2), args.(n - 1))

let op_fun h args = if Array.length args = 6 then Constr.mkApp (h, Array.sub args 0 4) else h

(* A reader of Nat values and certificates ([value], [certify]): the rows it reads, Lean's [/] when it reads a
   division, and its memos per term and per constant. The ordinary reader ([st.nat]: the Nat holes, the Fin case,
   the entry's gates) reads the rows of [op_specs]; the evaluator's reader of literal arithmetic ([ev_reader]) those
   and the [Sub] row of [ev_op_specs], in that order, and Lean's [/]. *)
type nat_reader = {
  form_rows : op_row list;
  div : div_reader option;
  values : Z.t option C.memo;
  const_values : (Constant.t, Z.t option) C.table;
  certs : (Z.t * Constr.t * int) option C.memo;
  const_certs : (Constant.t, (Z.t * Constr.t * int) option) C.table;
}

let nat_reader form_rows div =
  {
    form_rows;
    div;
    values = C.memo ();
    const_values = C.constant_table ();
    certs = C.memo ();
    const_certs = C.constant_table ();
  }

(* A reader of the Fin case ([fin_read]): the values it keeps are below [ceiling]; the divisor of a [%] is read
   by [value], with no ceiling, when [divisor_by_value] (the Fin values: the kernel compares a divisor and does
   not compute it), else by the reader itself (the parameters); its memo per term and per constant. *)
type reader = {
  ceiling : Z.t;
  divisor_by_value : bool;
  rmemo : Z.t option C.memo;
  rconsts : (Constant.t, Z.t option) C.table;
}

(* Literal arithmetic's view of the export at one entry ([setup_l], when [l_refs ()] is [Some]). *)
type lstate = {
  lr : l_refs;
  ev_reader : nat_reader;  (** the evaluator's reader *)
  divs : Constant.t list op_names;  (** Lean's [/] (the Fin case's [div] row's constants) *)
  held : Constant.t list;  (** the functions it holds: Lean's [Nat.add], [mul], [pow], [sub], [div], [mod] *)
  beqs : Constant.t list;  (** Lean's [Nat.beq]: computed on two literals below [hold_min], never held *)
  bles : Constant.t list;  (** Lean's [Nat.ble]: the same *)
  decides : Constant.t list;  (** Lean's [Decidable.decide] *)
  decide_thms : Constant.t list;  (** Lean's [decide_eq_true] *)
  dvds : Constant.t list;  (** Lean's [Dvd.dvd] *)
  instdvds : Constant.t list;  (** Lean's [Nat.instDvd] *)
  bool : (inductive * Univ.Level.t) option;  (** Lean's [Bool] and its level, from [Decidable.decide]'s type *)
  nonneg : inductive option;  (** Lean's [Int.NonNeg], from the body of [Int.le] *)
  pred : (Constr.t * Constr.t) option;  (** the export's [Nat.pred] without universes and its [toN_pred] proof *)
  ctors : (constructor, int * bool array) C.table;  (** [ctor_info], per constructor *)
}

(* The pass at one entry: the budget of its parts and the memos of the charged term layer ([ch]), the entry's
   view of the export, which [setup] reads once, and the memos and results of the pass. *)
type state = {
  ctx : context;
  refs : refs;
  ch : C.t;
  entry : Id.t;
  rows : op_row list;
  l : lstate option;  (** literal arithmetic's view of the export; [None] when it is off ([l_refs]) *)
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
  nat : nat_reader;  (** the ordinary reader *)
  fin_reader : reader;  (** [fin_value] *)
  param_reader : reader;  (** [param_value] *)
  nat_lits : (Z.t, Constr.t) C.table;  (** the literals [nat_lit] built, by value: one term per value and entry *)
  lit_memo : bool C.memo;  (** [is_literal], at the root of the term asked about *)
  walk_memo : bool C.memo;  (** [walk_literal]'s answers, at the root of the term asked about *)
  walk_lits : Constr.t array;  (** the literals [transport_walk] met last, the last met first ([walk_literal]) *)
  mutable walk_lits_n : int;  (** how many of [walk_lits] hold a literal *)
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

(* Whether [h] is [Nat_double]. *)
let is_double_head nt h =
  match Constr.kind h with Constr.Const (k, _) -> Constant.CanOrd.equal k nt.nt_double | _ -> false

(* Whether the declaration has no universe of its own; [mono_const] reads it (one step). *)
let mono cb = UVars.AbstractContext.is_empty (Declareops.constant_polymorphic_context cb)

let mono_const ch k = match C.const_decl ch k with Some cb -> mono cb | None -> false

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

(* The one recognizer of the Nat forms, by the reader [r] (the rows it reads, and Lean's [/] when it reads one):
   every guard is here. A constant of type Nat unfolds to its value, read by the charged body reader of
   LeanChargedTerm. *)
let nat_form st r depth c =
  let nt = st.refs in
  let h, args = Constr.decompose_app c in
  let nargs = Array.length args in
  match Constr.kind h with
  | Constr.Construct ((ind, 1), _) when nargs = 0 && Ind.CanOrd.equal ind nt.nt_nat -> Some Zero
  | Constr.Construct _ when nargs = 1 && is_nat_succ nt h -> Some (Succ args.(0))
  | Constr.Const _ when nargs = 1 && is_double_head nt h -> Some (Double args.(0))
  | Constr.Const (k, u) when nargs = 0 -> (
    match C.const_decl st.ch k with
    | Some cb when is_nat_ind nt cb.Declarations.const_type ->
      Option.map (fun b -> Unfold b) (C.def_body st.ch depth u cb)
    | Some _ | None -> None)
  | Constr.Const (k, _)
    when nargs = 3 && mem_const st k st.of_nat && is_nat_ind nt args.(0)
         && pat_matches st (Inst (st.inst_of_nat, [ Any ])) args.(2) ->
    Some (Unfold (snd (Constr.decompose_app args.(2))).(0))
  | Constr.Const (k, _) when nargs = 6 || nargs = 2 -> (
    match List.find_opt (fun row -> is_op st row.op_consts k args) r.form_rows with
    | Some row -> Some (Op (row, h, args))
    | None -> (
      match r.div with Some dv when is_op st dv.div_op k args -> Some (Div (dv, args)) | Some _ | None -> None))
  | _ -> None

(* The memo of [c]: its constant's table when it is a constant without universe instance, which never evicts
   (its miss needs no slot), else its own slot. *)
let memo_find st phys consts c =
  match Constr.kind c with
  | Constr.Const (k, u) when UVars.Instance.is_empty u -> (
    match C.table_find st.ch consts k with Some v -> C.Hit v | None -> C.Miss 0)
  | _ -> C.memo_find st.ch phys c

let memo_add st phys consts c slot v =
  match Constr.kind c with
  | Constr.Const (k, u) when UVars.Instance.is_empty u -> C.table_add st.ch consts k v
  | _ -> C.memo_set st.ch phys slot c v

(* The term under a run of [Nat_succ] applications, and [j] plus the length of the run: one step each, as
   [compute] charges a node, in a loop. *)
let rec succ_run st c j =
  match Constr.kind c with
  | Constr.App (h, [| x |]) when is_nat_succ st.refs h ->
    C.tick st.ch 1;
    succ_run st x (j + 1)
  | _ -> (c, j)

(* The value of the closed Nat term [c] by the reader [r], the nesting checked before the memo is read. A term
   is computed again only when its slot of the reader's memo holds another term; a constant without universe
   instance is kept in a table, which never evicts, so it is computed once per entry and reader. *)
let rec value st r depth c =
  C.check_depth depth;
  match memo_find st r.values r.const_values c with
  | C.Hit v -> v
  | C.Miss slot ->
    let v = compute st r depth c in
    memo_add st r.values r.const_values c slot v;
    v

and compute st r depth c =
  C.tick st.ch 1;
  match nat_form st r depth c with
  | None -> None
  | Some f ->
    let value = value st r (depth + 1) in
    (match f with
    | Zero -> Some Z.zero
    | Succ m ->
      (* [c] is [Nat_succ] applied [j] times to [b]; its value is the largest of the run, the one bounded *)
      let b, j = succ_run st m 1 in
      Option.bind (value b) (fun v -> bounded (Z.add v (Z.of_int j)))
    | Double m -> Option.bind (value m) (fun v -> bounded (Z.shift_left v 1))
    | Unfold b -> value b
    | Op (row, _, args) -> (
      let a, b = operands args in
      match (value a, value b) with Some x, Some y -> row.spec.z x y | _ -> None)
    | Div (_, args) -> (
      let a, b = operands args in
      match (value a, value b) with Some x, Some y -> Some (nat_div x y) | _ -> None))

(* The number of [Nat_succ] and [Nat_double] applications of [c] when it is a literal of the importer's form, read
   from the term itself, and -1 when it is none: the walk down those applications, one step each besides
   [nat_form]'s, the nesting checked at each. *)
let literal_levels st depth c =
  let rec walk depth n c =
    C.check_depth depth;
    match nat_form st st.nat depth c with
    | Some Zero -> n
    | Some (Succ m | Double m) ->
      C.tick st.ch 1;
      walk (depth + 1) (n + 1) m
    | Some (Unfold _ | Op _ | Div _) | None -> -1
  in
  walk depth 0 c

(* Whether [c] is a literal of the importer's form ([literal_levels]), the answer kept at the root of the term asked
   about in the entry's memo, so that a literal read again (as every operand of a held operation is, several times
   in a pair) costs a memo step, whatever its length; the suffixes of a long literal are never put in the memo,
   where they would share one slot and evict one another. *)
let is_literal st depth c =
  C.check_depth depth;
  match C.memo_find st.ch st.lit_memo c with
  | C.Hit b -> b
  | C.Miss slot ->
    let b = literal_levels st depth c >= 0 in
    C.memo_set st.ch st.lit_memo slot c b;
    b

(* The most literals [walk_literal] keeps, and the fewest levels of a literal it keeps. *)
let walk_lits_max = 16

(* Whether [c], an application of [Nat_succ] or [Nat_double] that [transport_walk] meets, is a literal of the
   importer's form: as [is_literal], with a memo of the walk's own ([walk_memo]), so that the walk leaves every memo
   that literal arithmetic and the arguments' parts read as it was (and their charges with it). Every unary literal
   of 10 or more has the same slot of such a memo (its hash reads at most ten [Nat_succ] of the term), so at a walk
   through [1024] and [4096] in turn the slot holds the other one: at a miss the walk also reads the literals of
   [walk_lits_max] levels or more it met last ([walk_lits], the last met first, at most [walk_lits_max]), one step
   for each it compares (by physical identity), before [literal_levels]. A literal found there moves first; one of
   [walk_lits_max] levels or more that [literal_levels] finds goes first, the last dropped when [walk_lits_max] are
   kept, so that keeping it costs no more than its walk did: a step for it and for each literal moved one place
   behind it. The memo's slot keeps the answer either way. *)
let walk_literal st depth c =
  C.check_depth depth;
  match C.memo_find st.ch st.walk_memo c with
  | C.Hit b -> b
  | C.Miss slot ->
    let lits = st.walk_lits and n = st.walk_lits_n in
    (* [c] first, the [i] literals before it moved one place *)
    let first i =
      C.tick st.ch (i + 1);
      Array.blit lits 0 lits 1 i;
      lits.(0) <- c
    in
    let rec recent i =
      if i = n then false
      else begin
        C.tick st.ch 1;
        if lits.(i) == c then begin
          first i;
          true
        end
        else recent (i + 1)
      end
    in
    let b =
      recent 0
      || begin
           let levels = literal_levels st depth c in
           if levels >= walk_lits_max then begin
             let kept = min n (walk_lits_max - 1) in
             first kept;
             st.walk_lits_n <- kept + 1
           end;
           levels >= 0
         end
    in
    C.memo_set st.ch st.walk_memo slot c b;
    b

(* [h] (the head of a [Nat_succ] application) applied [j] times to [b], each application charged. *)
let rebuild_succ st h j b =
  let rec go k acc = if k = 0 then acc else go (k - 1) (C.app_ch st.ch h [| acc |]) in
  go j b

(* [c] = [h x], [h] [Nat_succ] and [x] no literal: the run of [Nat_succ] from [c] walked in one loop
   ([succ_run]), its base [f] of its depth (the run's last [Nat_succ]'s), the nesting checked first, and the run
   rebuilt on [f]'s result only when that is another term. *)
let map_succ_run st depth c h x f =
  let b, j = succ_run st x 1 in
  C.check_depth (depth + j);
  let b' = f (depth + j) b in
  if b' == b then c else rebuild_succ st h j b'

(* The literal [c] unfolds to, if it is one: the kernel converts two terms of the same literal without
   arithmetic. *)
let rec literal_of st depth c =
  C.check_depth depth;
  if is_literal st depth c then Some c
  else
    match nat_form st st.nat depth c with
    | Some (Unfold b) ->
      C.tick st.ch 1;
      literal_of st (depth + 1) b
    | Some (Zero | Succ _ | Double _ | Op _ | Div _) | None -> None

(* The export's function of [row] without universes, as a term, and its [toN] lemma, kept per operation. *)
let rec lemma_of st row =
  match List.assoc_opt row.spec.op st.lemma_ops with
  | Some l -> l
  | None ->
    let g =
      List.find_map
        (fun c -> if mono_const st.ch c then Some (Constr.mkConstU (c, UVars.Instance.empty)) else None)
        row.op_consts.funs
    in
    let pred = match st.l with Some ls -> ls.pred | None -> None in
    let l =
      Option.bind g (fun g ->
          let prev =
            Option.bind row.spec.prev (fun op -> lemma_of st (List.find (fun row -> row.spec.op = op) st.rows))
          in
          Option.map
            (fun args -> (g, app (lib_term row.spec.to_n_lemma) args))
            (row.spec.lemma_args st.refs ~prev ~pred g))
    in
    st.lemma_ops <- (row.spec.op, l) :: st.lemma_ops;
    l

(* The literal of [v] in the importer's form ([large_literal] from [max_nat_int] on), so that the kernel compares
   it term for term with the importer's literals and with the predecessors it reduces them to. Its nodes are
   charged before they are built; [v] has at most [max_bits] bits. The entry's table keeps each literal built by its
   value: a literal asked for again costs a lookup and is the same term, so that the evaluation's memos (by physical
   identity) and [is_literal]'s answer for it are read again, instead of a fresh term of thousands of nodes being
   built and walked at each use. *)
let nat_lit st v =
  match C.table_find st.ch st.nat_lits v with
  | Some t -> t
  | None ->
    let nt = st.refs in
    let t =
      if Z.lt v max_nat_int then begin
        C.tick st.ch (Z.to_int v + 1);
        let succ = Constr.mkConstructU ((nt.nt_nat, 2), UVars.Instance.empty) in
        let rec succs k c = if k = 0 then c else succs (k - 1) (Constr.mkApp (succ, [| c |])) in
        succs (Z.to_int v) (nat_zero nt)
      end
      else begin
        C.tick st.ch (lit_succs v + (2 * Z.numbits v));
        large_literal nt.nt_nat (Constr.mkConstU (nt.nt_double, UVars.Instance.empty)) v
      end
    in
    C.table_add st.ch st.nat_lits v t;
    t

(* The declared type of the constant [k] (a theorem of Lean's library, without universes), its first binders
   instantiated by [args], then its next [n] hypotheses (independent ones) and its conclusion; [None] when it has
   not that shape. Its declaration read once, each binder and substitution charged. *)
let theorem_parts st depth k args n =
  match C.const_decl st.ch k with
  | Some cb when mono cb ->
    let rec inst ty = function
      | [] -> Some ty
      | a :: rest -> (
        C.tick st.ch 1;
        match Constr.kind ty with Constr.Prod (_, _, b) -> inst (C.subst1_ch st.ch depth a b) rest | _ -> None)
    in
    let rec hyps ty n acc =
      if n = 0 then Some (List.rev acc, ty)
      else begin
        C.tick st.ch 1;
        match Constr.kind ty with
        | Constr.Prod (_, h, b) when C.closed st.ch depth b ->
          hyps (C.subst1_ch st.ch depth Constr.mkProp b) (n - 1) (h :: acc)
        | _ -> None
      end
    in
    Option.bind (inst cb.Declarations.const_type args) (fun ty -> hyps ty n [])
  | Some _ | None -> None

(* The two sides of Lean's [LE.le Nat _ x y] or [LT.lt Nat _ x y]. *)
let rel_sides c =
  let _, args = Constr.decompose_app c in
  if Array.length args = 4 then Some (args.(2), args.(3)) else None

(* [e : P c] turned into a proof of [P t], [motive] = [P], where [c] (the form a Lean theorem states) and [t]
   (the form the pass reads, [Nat.div a b] for [HDiv.hDiv Nat Nat Nat _ a b]) apply their heads to the same
   last two arguments [a], [b]: [e] is cast along [bridge a b], [bridge] =
   [fun x y => (eq_refl (t x y) : c x y = t x y)]. The kernel checks that cast once on the two variables, where
   both sides stop at a match on a variable, and never compares [c] with [t] at literals: there it unfolds
   [Nat.div] first and computes on the unary [Nat] (the lemma [2^26 - 1 = Nat.div (2^32 - 1) 64] took more than
   120 s in its declaration). [None] when the two terms do not have that shape. Each comparison, lift and copy
   charged. *)
let bridge st depth c t motive e =
  if C.equal st.ch depth c t then Some e
  else
    let nt = st.refs in
    let hc, ac = Constr.decompose_app c and ht, at = Constr.decompose_app t in
    let nc = Array.length ac and n_t = Array.length at in
    if
      nc < 2 || n_t < 2
      || not (C.equal st.ch depth ac.(nc - 2) at.(n_t - 2) && C.equal st.ch depth ac.(nc - 1) at.(n_t - 1))
    then None
    else begin
      C.tick st.ch (nc + n_t);
      let abs h args n =
        Constr.mkApp
          ( C.lift_ch st.ch depth 2 h,
            Array.append (Array.map (C.lift_ch st.ch depth 2) (Array.sub args 0 (n - 2))) [| r2; r1 |] )
      in
      let cx = abs hc ac nc and tx = abs ht at n_t in
      let nat = nat_type nt in
      let refl = Constr.mkConstructU ((nt.nt_eq, 1), eq_inst) in
      let body = Constr.mkCast (app refl [| nat; tx |], Constr.DEFAULTcast, eq_nat nt cx tx) in
      let lam n b = Constr.mkLambda (Context.nameR (Id.of_string n), nat, b) in
      Some (app nt.nt_transport [| motive; c; t; app (lam "x" (lam "y" body)) [| ac.(nc - 2); ac.(nc - 1) |]; e |])
    end

(* [Nat_le_of_toN x y nx ny px py (eq_refl true)]: [x <= y] from the binary literals [nx], [ny] of their values and
   the certificates [px], [py], the kernel comparing the two literals with [N.leb]. *)
let le_of_toN st lr x y nx ny px py =
  app lr.lr_le_of_toN [| x; y; nx; ny; px; py; app st.refs.nt_refl [| lr.lr_bool; lr.lr_true |] |]

(* The parts of Lean's [Nat.div_eq_of_lt_le k b a] ([thm]) that [certify_div] proves: the left side of its
   hypothesis [k * b ≤ a], the right side of [a < (k + 1) * b] and the form of [a / b] its conclusion states. *)
let div_statement st depth thm k a b =
  match theorem_parts st depth thm [ k; b; a ] 2 with
  | Some ([ lo_ty; hi_ty ], concl) -> (
    match (rel_sides lo_ty, rel_sides hi_ty, snd (Constr.decompose_app concl)) with
    | Some (x_lo, _), Some (_, z_hi), [| _; c; _ |] -> Some (x_lo, z_hi, c)
    | _ -> None)
  | Some _ | None -> None

(* The value [v] of [t] by the reader [r], a proof of [Logic.eq (toN t) w] for [w] the binary literal of [v], and
   the size of that proof; [None] when [t] has no value or an operation it needs has no [toN] lemma. Every step
   states its own term, so that the kernel only compares a term with itself, and checks each binary operation on
   literals. A proof built once is used again, its size counted again. The nesting is checked before the memo
   is read. [known] is [t]'s value when the caller has it: a literal's successor, double or unfolded term
   gets it from its parent's (v - 1, v / 2, v), so that a chain is valued once, from its top; computed again at
   each node, its suffixes, which evict one another from the reader's memo, would cost about [n * n] steps for
   a chain of [n] nodes. *)
let rec certify ?known st r depth t =
  C.check_depth depth;
  match memo_find st r.certs r.const_certs t with
  | C.Hit res ->
    (match res with Some (_, _, size) -> C.tick st.ch size | None -> ());
    res
  | C.Miss slot ->
    let res = certify_node ?known st r depth t in
    memo_add st r.certs r.const_certs t slot res;
    res

and certify_node ?known st r depth t =
  let nt = st.refs in
  match (match known with Some v -> Some v | None -> value st r depth t) with
  | None -> None
  | Some v ->
    C.tick st.ch 1;
    let w = n_literal nt v in
    if Z.lt v small_literal && is_literal st depth t then Some (v, refl_n nt w, 1)
    else
      (* The current part has paid each child's size (the child was built in it, or [certify] charged its full
         size again on reuse) and this node's step, all within its budget of at most [max_int] steps: so the
         sums of sizes below, each at most what this part paid, cannot overflow. *)
      let sub m = certify st r (depth + 1) m in
      let step lemma m vm =
        Option.map
          (fun (vm, pm, sm) -> (v, app lemma [| m; n_literal nt vm; w; pm; refl_n nt w |], sm + 1))
          (certify ~known:vm st r (depth + 1) m)
      in
      (match nat_form st r depth t with
      | Some Zero -> Some (v, refl_n nt w, 1)
      | Some (Succ m) -> step nt.nt_succ_step m (Z.pred v)
      | Some (Double m) -> step nt.nt_double_step m (Z.shift_right v 1)
      | Some (Unfold b) ->
        Option.map
          (fun (_, pb, sb) -> (v, app nt.nt_unfold_step [| t; b; w; refl_nat nt t; pb |], sb + 1))
          (certify ~known:v st r (depth + 1) b)
      | Some (Op (row, h, args)) ->
        let f = op_fun h args and a, b = operands args in
        (match (lemma_of st row, sub a, sub b) with
        | Some (g, hg), Some (va, pa, sa), Some (vb, pb, sb) ->
          let hfg = lam2 nt (refl_nat nt (app (C.lift_ch st.ch depth 2 f) [| r2; r1 |])) in
          let hn = lib_term row.spec.n_fun in
          Some
            ( v,
              app nt.nt_op_step
                [| f; g; hn; hfg; hg; a; b; n_literal nt va; n_literal nt vb; w; pa; pb; refl_n nt w |],
              sa + sb + 1 )
        | _ -> None)
      | Some (Div (dv, args)) ->
        let a, b = operands args in
        certify_div st r dv depth t v a b
      | None -> None)

(* [t] = [a / b] of value [v] = [q], [b] positive: Lean's [Nat.div_eq_of_lt_le q b a lo hi : a / b = q] with
   [lo : q * b ≤ a] and [hi : a < (q + 1) * b] proved by [Nat_le_of_toN] from the binary values, which the
   kernel compares with [N.leb]; then [toN_of_eq]. Each binary literal it builds is charged by its nodes before it
   is built. [None] when the theorem is not declared, or not of that shape. *)
and certify_div st r dv depth t v a b =
  let sub = certify st r (depth + 1) in
  match (dv.div_thms, sub a, sub b) with
  | thm :: _, Some (va, pa, sa), Some (vb, _, sb) when Z.sign vb > 0 -> (
    let k = nat_lit st v in
    match div_statement st depth thm k a b with
    | None -> None
    | Some (x_lo, z_hi, c) -> (
      match (sub x_lo, sub k, sub z_hi) with
      | Some (vx, px, sx), Some (_, pk, sk), Some (vz, pz, sz) -> (
        C.tick st.ch 12;
        let nt = st.refs and lr = dv.div_lr in
        let lit z =
          C.tick st.ch (n_literal_nodes z);
          n_literal nt z
        in
        let motive = Constr.mkLambda (Context.nameR (Id.of_string "z"), nat_type nt, eq_nat nt r1 k) in
        let nvx = lit vx and nva = lit va and nva1 = lit (Z.succ va) and nvz = lit vz in
        let lo = le_of_toN st lr x_lo a nvx nva px pa in
        let pa1 = app nt.nt_succ_step [| a; nva; nva1; pa; refl_n nt nva1 |] in
        let hi = le_of_toN st lr (nat_succ nt a) z_hi nva1 nvz pa1 pz in
        let e = app (Constr.mkConstU (thm, UVars.Instance.empty)) [| k; b; a; lo; hi |] in
        match bridge st depth c t motive e with
        | Some e -> Some (v, app lr.lr_of_eq [| t; k; lit v; e; pk |], sa + sb + sx + sk + sz + 3)
        | None -> None)
      | _ -> None))
  | _ -> None

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

(* The kernel refused a lemma the pass generated: the argument whose transport generated it (its hole's lemma, or
   a sub-lemma generated while its holes are found) keeps Lean's term ([transport_arg_in]). No refusal is
   remembered: a later argument generates its lemmas again. *)
exception Refused

(* Declare [proof] as the lemma [x = y] at the type [ty] of level [level] (src/Lean.v's [eq@{level}]), named
   [<entry>__nat_eq_<k>] or, when that name is taken, the next free one as [Namegen] counts them (each name it
   tries charged), and keep it for a later place with the same two terms. A lemma the kernel refuses is logged,
   and [Refused] raised. *)
let declare_eq_at st ty level x y proof =
  let nt = st.refs in
  let lemma_ty = app (Constr.mkIndU (nt.nt_eq, inst1 level)) [| ty; x; y |] in
  st.next <- st.next + 1;
  let id = Id.of_string (Id.to_string st.entry ^ "__nat_eq_" ^ string_of_int st.next) in
  let taken id =
    C.tick st.ch 1;
    Global.exists_objlabel id
  in
  let id = if taken id then Namegen.next_ident_away_from id taken else id in
  match st.ctx.declare id lemma_ty proof with
  | GlobRef.ConstRef c ->
    lemma_cache := ((x, y), c) :: !lemma_cache;
    c
  | GlobRef.VarRef _ | GlobRef.IndRef _ | GlobRef.ConstructRef _ -> assert false
  | exception e when CErrors.noncritical e ->
    st.ctx.log (refused_lemma_msg id x y proof e);
    raise Refused

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

(* The lemma [x = y] at [ty] of level [level] for two closed terms, at the nesting [depth] of the place that needs
   it: the file's cached one, or one declared on first use with the proof [proof ()]; [None] when the terms do
   not pass [lemma_terms_ok] or [proof ()] is [None]; [Refused] when the kernel refuses it. *)
let eq_lemma_at st depth ty level x y proof =
  match cached_nat_eq st depth x y with
  | Some c -> Some c
  | None -> (
    if not (lemma_terms_ok st depth x y) then None
    else match proof () with Some p -> Some (declare_eq_at st ty level x y p) | None -> None)

(* The same at Nat. *)
let eq_lemma st depth x y proof = eq_lemma_at st depth (nat_type st.refs) Univ.Level.set x y proof

(* The proof of [x = y] for two closed Nat terms of equal value by the reader [r]: through Rocq's binary [N]. *)
let nat_eq_proof st r depth x y () =
  match (certify st r depth x, certify st r depth y) with
  | Some (vx, cx, _), Some (vy, cy, _) when Z.equal vx vy ->
    Some (app st.refs.nt_nat_eq [| x; y; n_literal st.refs vx; cx; cy |])
  | _ -> None

(* The lemma [x = y] at Nat by the reader [r]'s certificates, as a term. *)
let nat_lemma st r depth x y =
  Option.map (fun c -> Constr.mkConstU (c, UVars.Instance.empty)) (eq_lemma st depth x y (nat_eq_proof st r depth x y))

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
   two closed terms that reduce to the same constructors down to a [Fin] whose values are closed Nat terms of
   equal value [fv] ([Fin_hole]), or (literal arithmetic, [ec_hole]) two closed terms of the closed type [vty], of
   level [vlevel], that the evaluation proves equal by [vproof], cast by [vcast] ([sprop_transport_any] at
   [vlevel]) ([Val_hole]). *)
type hole =
  | Nat_hole of Constr.t * Constr.t
  | Fin_hole of { fa : Constr.t; fd : Constr.t; sa : fin_side; sd : fin_side; fv : Z.t }
  | Val_hole of {
      va : Constr.t;
      vd : Constr.t;
      vty : Constr.t;
      vlevel : Univ.Level.t;
      vproof : Constr.t;
      vcast : Constr.t;
    }

let hole_terms = function
  | Nat_hole (x, y) -> (x, y)
  | Fin_hole { fa; fd; _ } -> (fa, fd)
  | Val_hole { va; vd; _ } -> (va, vd)

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
    match nat_form st st.nat depth c with
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
  | C.Hit v -> v
  | C.Miss slot ->
    let v = fin_read_node st r depth c in
    memo_add st r.rmemo r.rconsts c slot v;
    v

and fin_read_node st r depth c =
  C.tick st.ch 1;
  let below v = if Z.lt v r.ceiling then Some v else None in
  let read = fin_read st r (depth + 1) in
  let both x y f = match (read x, read y) with Some a, Some b -> Option.bind (f a b) below | _ -> None in
  match fin_form st depth c with
  | Some (Mod (x, y)) -> (
    let divisor = if r.divisor_by_value then value st st.nat (depth + 1) y else read y in
    match (read x, divisor) with Some a, Some b when Z.sign b > 0 -> below (Z.rem a b) | _ -> None)
  | Some (Form Zero) -> Some Z.zero
  | Some (Form (Unfold b)) -> read b
  | Some (Form (Succ x)) ->
    (* [c] is [Nat_succ] applied [j] times to [b]; its value is the largest of the run *)
    let b, j = succ_run st x 1 in
    Option.bind (read b) (fun v -> below (Z.add v (Z.of_int j)))
  | Some (Form (Double x)) -> Option.bind (read x) (fun v -> below (Z.shift_left v 1))
  | Some (Form (Op (row, _, args))) ->
    let x, y = operands args in
    both x y row.spec.z
  | Some (Form (Div _)) -> None (* the ordinary reader reads no division *)
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

exception Found

(* Whether [c], at the nesting [depth], has a closed Nat subterm of value [bound] or more by the ordinary reader,
   each node charged: the gate of the Nat case ([transport_min]) and of a held [decide]'s proposition
   ([hold_min]). *)
let has_nat_from st bound depth c =
  let rec scan depth c =
    C.tick st.ch 1;
    C.check_depth depth;
    match value st st.nat depth c with
    | Some v -> if Z.geq v bound then raise_notrace Found
    | None -> Constr.iter (scan (depth + 1)) c
  in
  try
    scan depth c;
    false
  with Found -> true

(* ---- Literal arithmetic: the evaluation of closed terms of a data type ----

   A pair [a], [d] of closed terms of a data type ([Bool], [Int], omega's [Constraint], or a Nat term the
   ordinary reader gives no value) whose conversion needs a Nat operation on a large literal
   ([Nat.sub 16 4294967296] inside [decide (Constraint.isImpossible ...)], [Nat.div 4294967295 4096] inside
   [tidyConstraint]): Rocq's kernel computes it on the unary [Nat]. [ec_eval] evaluates each side in rounds: a
   round reduces the term to its normal form ([ev_nf], each head step by [ev_head]), with each held operation
   left as it is, then puts the value of each in its place. A Nat operation ([Nat.add], [mul], [pow], [sub],
   [div], [mod]) is held when an operand or its value is [hold_min] or more, or an operand is held; below that
   the evaluation computes it and so does the kernel. [Nat.beq] and [Nat.ble] are never held: on two literals
   below [hold_min] the evaluation computes their Bool constructor, on anything else the pair gets no lemma. A
   held [%], a [Nat.mod] with a value anywhere in a normal form, and an operation the evaluation cannot value (an
   operand with no value, a value of more than [max_bits] bits), give the pair no lemma. A closed
   [decide p inst] whose proposition holds a Nat term of [hold_min] or more is held as a whole, its value [true]
   proved by Lean's [decide_eq_true] from a proof of [p] ([prove_prop]). A match, a fixpoint or a projection whose
   scrutinee, recursive argument or subject is a constructor is contracted (the first class); one that waits on a
   held operation is left as it is for that round (the second class), and gives the pair no lemma when it still
   waits after the last round; anything else gives the pair no lemma at once (the third class, [Eval_stop]). The
   proof of [t = v] goes back through the rounds: [eq_refl v] is cast, along a lemma [l = s] for each held
   operation [s] of value [l], from [N[l]] to [N[s]]; the kernel converts [N[l]] with the next round's normal
   form, and [t] with the first one. Every step is charged before it, and an outer pair's charges, its nested
   evaluations included, are at most [pair_cap] ([C.with_pair]); a pair declined at the cap leaves its charges in
   the argument's part, and no node pair inside it is evaluated ([nat_diff]).

   The evaluation substitutes closed terms without copying them ([C.subst_closed]), so a term it builds is a
   graph whose tree may hold far more nodes than the charges that built it. Each walker of the evaluation's terms
   pays its own walk: [ev_whnf] and [ev_head] a step per head reduction and per read and write of the round's memo
   (by pointer); [ev_nf], [ev_nat] and [ev_ctor] a visit per node of the tree; [ec_canon], [held_ops] and
   [fill_ops] [C.node_steps] per node of the tree, [fill_ops] also a step per operation compared; the first five
   read a literal of the importer's form at once ([is_literal]'s memo); [nf_compare] and [C.equal] a visit per
   pair of nodes compared, a physically equal pair at once; [value], [is_literal], [certify] and [certify_div] a
   step per node computed, memoized by pointer or constant; [C.whd], [C.type_of], [type_level], [C.expose_sort]
   and [has_nat_from] each step and substitution, a replacement placed again by its size; [C.free] and
   [C.closed] [C.node_steps] at a miss; [C.size] a visit per node by pointer. What reaches the kernel is bounded by
   the charges: a lemma's statement pays the tree size of its two terms ([lemma_terms_ok]); each builder of the
   evaluation's proofs ([ec_proof], [eq_sym], [decide_lemma], [nonneg_proof], [ec_eq_proof]) pays the tree size of
   each term it places, at each place, before it builds ([pay_trees]); the Nat certificates ([certify],
   [nat_eq_proof]) place each statement term once more and a binary literal of at most [2 * max_bits + 1] nodes
   per step, charged by the step ([certify_div]'s by its nodes). A pair whose proof would need more than the cap
   is declined at the cap. *)

(* The most charges of one outer pair's evaluation, both sides, every round and every nested evaluation
   together; more, and the pair gets no lemma while the pass goes on. *)
let pair_cap = 200_000

(* The most replacement rounds of one side (of a pair or of a nested evaluation). *)
let max_rounds = 16

(* An operand or value from this one on makes the evaluation hold an operation: the kernel computes one below it
   on the unary [Nat] in about 0.5 s at most ([Nat.sub 32 65536] took 0.516 s). A stated bound, not a debit. *)
let hold_min = Z.of_int 65536

(* Whether the values are below [hold_min]: the evaluation computes an operation of such operands and value
   ([hold_op], [compare_arm]), and holds no other ([canon_held], [held_ops]). *)
let below_hold vs = List.for_all (fun v -> Z.lt v hold_min) vs

(* The value function and operands of a form the evaluation holds: an [Op] of a row, or a [Div] ([class_arm],
   [ec_canon]). *)
let held_operands = function
  | Some (Op (row, _, args)) ->
    let a, b = operands args in
    Some (row.spec.z, a, b)
  | Some (Div (_, args)) ->
    let a, b = operands args in
    Some ((fun x y -> Some (nat_div x y)), a, b)
  | Some (Zero | Succ _ | Double _ | Unfold _) | None -> None

(* The evaluation that met it ends: an outer pair gets no lemma, a nested evaluation no proof. *)
exception Eval_stop

(* The evaluation of one pair or one nested evaluation: the round's memo of [ev_whnf], its table of held
   operations and their representatives ([held_rep]), the representatives themselves, and its wait (a match,
   fixpoint or projection waits on a held operation in this round), all fresh at each round ([new_round]);
   whether it held any operation, and whether it held one at a position the evaluation evaluates ([ev_head]'s
   [hold_op] or held [decide]), which a lemma needs ([ec_eq_proof]). *)
type ev = {
  mutable ev_memo : Constr.t C.memo;
  mutable ev_tab : (Constant.t * Z.t * Z.t, (Constr.t * Constr.t * Constr.t * Constr.t) list ref) C.table;
  mutable ev_reps : Constr.t list;
  mutable ev_wait : bool;
  mutable ev_held : bool;
  mutable ev_held_eval : bool;
}

let new_ev () =
  {
    ev_memo = C.memo ();
    ev_tab = C.held_table ();
    ev_reps = [];
    ev_wait = false;
    ev_held = false;
    ev_held_eval = false;
  }

(* The start of a round: no memo entry, representative or wait of an earlier round is read again. *)
let new_round ev =
  ev.ev_memo <- C.memo ();
  ev.ev_tab <- C.held_table ();
  ev.ev_reps <- [];
  ev.ev_wait <- false

(* The round's representative of the held operation [t] = [f a b] on the values [va] and [vb], of head constant
   [k] and form [f] (Lean's function, or its class function applied to the same type arguments and instance): the
   first occurrence of that form on the same operands, the forms compared by [C.equal], two operands the same
   when they are the same term or unfold to the same literal ([literal_of]: [OfNat.ofNat Nat 65536 _] and the
   literal [65536]), each comparison charged. So every occurrence of one held operation in one form on one pair of
   operands is the same term, and an occurrence in another form, or on an operand of the same value in another
   form ([2 ^ 32] and the literal [4294967296]), has its own. The kernel then converts each occurrence with its
   representative by unfolding constants only, never one form or operand with another, which it may do by
   computing an operation on the unary [Nat]. *)
let held_rep st ev depth k f a b t va vb =
  let added () =
    ev.ev_held <- true;
    ev.ev_reps <- t :: ev.ev_reps;
    t
  in
  let same x y =
    C.equal st.ch depth x y
    ||
    match (literal_of st depth x, literal_of st depth y) with
    | Some lx, Some ly -> C.equal st.ch depth lx ly
    | _ -> false
  in
  let key = (k, va, vb) in
  match C.table_find st.ch ev.ev_tab key with
  | Some forms -> (
    match List.find_opt (fun (f', a', b', _) -> C.equal st.ch depth f f' && same a a' && same b b') !forms with
    | Some (_, _, _, r) -> r
    | None ->
      forms := (f, a, b, t) :: !forms;
      added ())
  | None ->
    C.table_add st.ch ev.ev_tab key (ref [ (f, a, b, t) ]);
    added ()

(* Whether [c] is one of the round's representatives, each compared charged. *)
let is_rep st ev c =
  List.exists
    (fun r ->
      C.tick st.ch 1;
      r == c)
    ev.ev_reps

(* The number of parameters of the inductive type of the constructor [cstr] and the relevance of each of its
   arguments after them, read once per entry and constructor, a miss charged by the constructor's context. *)
let ctor_info st ls ((ind, i) as cstr) =
  match C.table_find st.ch ls.ctors cstr with
  | Some r -> r
  | None ->
    let mib, mip = Inductive.lookup_mind_specif st.ch.C.genv ind in
    let ctx, _ = mip.Declarations.mind_nf_lc.(i - 1) in
    C.tick st.ch (1 + List.length ctx);
    let nreal = mip.Declarations.mind_consnrealdecls.(i - 1) in
    let rel =
      Array.of_list
        (List.rev_map
           (fun d -> Sorts.relevance_equal (Context.Rel.Declaration.get_relevance d) Sorts.Relevant)
           (CList.firstn nreal ctx))
    in
    let r = (mib.Declarations.mind_nparams, rel) in
    C.table_add st.ch ls.ctors cstr r;
    r

let ctor_app c =
  let h, args = Constr.decompose_app c in
  match Constr.kind h with Constr.Construct (cstr, _) -> Some (cstr, h, args) | _ -> None

(* Whether [c] is [Nat_double] applied to one argument: a literal's binary step, folded until a constructor is
   needed ([ev_ctor]). *)
let is_double st c = match Constr.kind c with Constr.App (h, [| _ |]) -> is_double_head st.refs h | _ -> false

(* [f] applied to [args], each leading lambda taking one ([C.beta_closed], every binder fits). The evaluation
   starts on a closed term and never goes under a binder, so each term it substitutes (an argument, a
   constructor's argument, a let's value, the fixpoint itself) is closed: [C.subst_closed] shares it. *)
let beta_app st depth f args = C.beta_closed st.ch depth f args

(* The body of a fixpoint with its [n] fixpoints substituted for its [n] names (the last for [Rel 1]): the [n]
   terms after [n] steps, then the charged substitution. *)
let contract_fix st depth ((ri, bodynum), ((_, _, bodies) as rd)) =
  let n = Array.length ri in
  C.tick st.ch n;
  C.subst_closed st.ch depth (Array.init n (fun j -> Constr.mkFix ((ri, j), rd))) 0 n bodies.(bodynum)

(* The value of a held operation: a Nat, or [true] of a held [decide p inst] with a proof of [p]. *)
type held_value = HNat of Z.t | HDec of Constr.t

let rec fun_row st k = function
  | [] -> None
  | row :: rows -> if mem_const st k row.op_consts.funs then Some row else fun_row st k rows

(* Whether [k] is one of the export's [Nat.mod], each comparison charged. *)
let is_mod st k = mem_const st k st.mod_op.funs

(* The value of the held function [k] on the operand values [a] and [b] (Lean's: [a / 0] is 0, [a % 0] is [a]);
   [None] when it has more than [max_bits] bits. Each comparison charged. *)
let op_value st ls k a b =
  if mem_const st k ls.divs.funs then Some (nat_div a b)
  else if is_mod st k then Some (if Z.equal b Z.zero then a else Z.rem a b)
  else match fun_row st k ls.ev_reader.form_rows with Some row -> row.spec.z a b | None -> None

let bool_ctor ls b =
  match ls.bool with
  | Some (ind, _) -> Some (Constr.mkConstructU ((ind, if b then 2 else 1), UVars.Instance.empty))
  | None -> None

(* Whether [c] is a held [decide p inst]: closed, its proposition holding a Nat term of [hold_min] or more. *)
let is_held_decide st ls depth c =
  match Constr.kind c with
  | Constr.App (h, [| p; _ |]) -> (
    match Constr.kind h with
    | Constr.Const (k, _) ->
      mem_const st k ls.decides && C.closed st.ch depth c && has_nat_from st hold_min (depth + 1) p
    | _ -> false)
  | _ -> false

(* A match's scrutinee, a fixpoint's recursive argument or a projection's subject [t], evaluated, that is not a
   constructor: a held operation (the second class: a held function, a held [decide] or a representative of a
   class function's form), which a later round may replace by its value (the round's wait records it), or
   anything else (the third class): [Eval_stop]. Unlike [held_ops]'s, the test reads no arity: [t] is [ev_whnf]'s
   result, whose held operations [hold_op] and [ev_head] built at the arities [held_ops] reads (two arguments for
   a held function or [decide], six for a representative of a class function's form). *)
let stuck st ls ev depth t =
  let held =
    match head_const t with
    | Some k -> mem_const st k ls.held || is_held_decide st ls depth t || is_rep st ev t
    | None -> false
  in
  if held then ev.ev_wait <- true else raise Eval_stop

(* [c], closed, in weak head normal form, a literal's [Nat_double] folded: the round's memo first (the nesting
   checked before it is read), then [ev_head], whose result the memo keeps at [c]. *)
let rec ev_whnf st ls ev depth c =
  C.check_depth depth;
  match C.memo_find st.ch ev.ev_memo c with
  | C.Hit r -> r
  | C.Miss slot ->
    let r = ev_head st ls ev depth c in
    C.memo_set st.ch ev.ev_memo slot c r;
    r

(* The one rule of the evaluation: [c] reduced at its head in a loop at one nesting level, each step charged
   before it: the unfolding of a transparent constant, beta, zeta, a cast;
   a match, a fixpoint applied to more arguments than its recursive index, or a projection, contracted once its
   scrutinee, recursive argument or subject, evaluated one level deeper ([ev_ctor]), is a constructor (the
   first class), left as it is with the round's wait set when that is a held operation (the second class),
   [Eval_stop] when it is anything else (the third class), and when a constructor's arguments are not as many as
   the branch binds or a projection's index is past them. It stops at a constructor, a literal's [Nat_double],
   a held operation ([held_arm], [class_arm]), a held [decide], an application whose head has no body, and any
   other term with no head step. *)
and ev_head st ls ev depth c =
  C.tick st.ch 1;
  let h, args = Constr.decompose_app c in
  let nargs = Array.length args in
  match Constr.kind h with
  | Constr.Construct _ -> c
  | Constr.Const _ when is_double st c -> c
  | Constr.Const (k, u) ->
    if nargs = 2 && is_held_decide st ls depth c then begin
      ev.ev_held <- true;
      ev.ev_held_eval <- true;
      c
    end
    else if nargs = 2 && mem_const st k ls.held then held_arm st ls ev depth h k args
    else if nargs = 2 && (mem_const st k ls.beqs || mem_const st k ls.bles) then compare_arm st ls ev depth h k u args
    else if nargs = 6 then class_arm st ls ev depth c h k u args
    else unfold st ls ev depth c k u args
  | Constr.Lambda _ when nargs > 0 -> ev_head st ls ev depth (beta_app st depth h args)
  | Constr.LetIn (_, v, _, b) -> ev_head st ls ev depth (C.app_ch st.ch (C.subst_closed st.ch depth [| v |] 0 1 b) args)
  | Constr.Cast (t, _, _) -> ev_head st ls ev depth (C.app_ch st.ch t args)
  | Constr.Case (ci, u, pms, p, iv, s, brs) -> (
    let s' = ev_ctor st ls ev (depth + 1) s in
    match ctor_app s' with
    | Some ((_, i), _, sargs) ->
      let nas, body = brs.(i - 1) in
      let npar = ci.Constr.ci_npar in
      let nreal = Array.length sargs - npar in
      if nreal <> Array.length nas then raise Eval_stop
      else begin
        C.tick st.ch (1 + nreal);
        ev_head st ls ev depth (C.app_ch st.ch (C.subst_closed st.ch depth sargs npar nreal body) args)
      end
    | None ->
      stuck st ls ev depth s';
      C.tick st.ch (C.node_steps h);
      C.app_ch st.ch (Constr.mkCase (ci, u, pms, p, iv, s', brs)) args)
  | Constr.Fix (((ri, i), _) as fix) when nargs > ri.(i) ->
    let r = ri.(i) in
    let args = C.sub_ch st.ch args 0 nargs in
    args.(r) <- ev_ctor st ls ev (depth + 1) args.(r);
    if Option.has_some (ctor_app args.(r)) then
      ev_head st ls ev depth (C.app_ch st.ch (contract_fix st depth fix) args)
    else begin
      stuck st ls ev depth args.(r);
      C.app_ch st.ch h args
    end
  | Constr.Proj (p, rel, s) -> (
    let s' = ev_ctor st ls ev (depth + 1) s in
    match ctor_app s' with
    | Some (_, _, sargs) ->
      let i = Projection.npars p + Projection.arg p in
      if i < Array.length sargs then ev_head st ls ev depth (C.app_ch st.ch sargs.(i) args) else raise Eval_stop
    | None ->
      stuck st ls ev depth s';
      C.tick st.ch 1;
      C.app_ch st.ch (Constr.mkProj (p, rel, s')) args)
  | _ -> c

(* A held function applied to two arguments ([hold_op] at its own form). *)
and held_arm st ls ev depth h k args =
  hold_op st ls ev depth k h (op_value st ls k) (fun () -> is_mod st k) args.(0) args.(1)

(* A class function at Nat's instance applied to its type arguments, instance and two operands, in a form the
   evaluator's reader reads (an [Op] of a row or a [Div]): held in that form ([hold_op]), never first unfolded to
   the function of its instance, so that it is the term the source holds, in the evaluated positions as in a
   match's return predicate or a dependent field's type; any other such application unfolds. The form [f] of an
   [Op] is built uncharged ([op_fun]), that of a [Div] charged. *)
and class_arm st ls ev depth c h k u args =
  let form = nat_form st ls.ev_reader depth c in
  match held_operands form with
  | Some (z, a, b) ->
    let f = match form with Some (Op _) -> op_fun h args | _ -> C.app_ch st.ch h (C.sub_ch st.ch args 0 4) in
    hold_op st ls ev depth k f z (fun () -> false) a b
  | None -> unfold st ls ev depth c k u args

(* The operation [f fa fb] of head constant [k] and value function [z]: each operand evaluated to a literal or a
   held operation ([ev_nat]) and read by the evaluator's reader. The literal of its value when the value and both
   operands are below [hold_min] and both operands are literals; else the operation is held, as the round's
   representative of its form and operand values. [Eval_stop] for a held [%] ([is_mod]: no certificate proves its
   value), an operand of no value and a value of more than [max_bits] bits. *)
and hold_op st ls ev depth k f z is_mod fa fb =
  let a = ev_nat st ls ev (depth + 1) fa in
  let b = ev_nat st ls ev (depth + 1) fb in
  match (value st ls.ev_reader depth a, value st ls.ev_reader depth b) with
  | Some va, Some vb -> (
    match z va vb with
    | Some v when below_hold [ va; vb; v ] && is_literal st (depth + 1) a && is_literal st (depth + 1) b ->
      nat_lit st v
    | Some _ when is_mod () -> raise Eval_stop
    | Some _ ->
      ev.ev_held_eval <- true;
      held_rep st ev depth k f a b (C.app_ch st.ch f [| a; b |]) va vb
    | None -> raise Eval_stop)
  | _ -> raise Eval_stop

(* [Nat.beq] and [Nat.ble] applied to two arguments: on two literals below [hold_min], their Bool constructor
   (the kernel converts the comparison); with no Lean [Bool] read ([setup_l]), unfolded as any constant; on
   anything else, the third class. *)
and compare_arm st ls ev depth h k u args =
  let a = ev_nat st ls ev (depth + 1) args.(0) in
  let b = ev_nat st ls ev (depth + 1) args.(1) in
  let small x =
    if is_literal st (depth + 1) x then
      match value st ls.ev_reader depth x with Some v when below_hold [ v ] -> Some v | Some _ | None -> None
    else None
  in
  match (small a, small b) with
  | Some va, Some vb -> (
    match bool_ctor ls (if mem_const st k ls.beqs then Z.equal va vb else Z.leq va vb) with
    | Some t -> t
    | None ->
      let args = [| a; b |] in
      unfold st ls ev depth (C.app_ch st.ch h args) k u args)
  | _ -> raise Eval_stop

(* The constant [k] at [u] applied to [args] ([c]): its body applied to them and reduced on, or [c] itself when it
   has no body (an axiom, an opaque constant, a primitive). *)
and unfold st ls ev depth c k u args =
  match C.const_decl st.ch k with
  | Some cb -> (
    match C.def_body st.ch depth u cb with
    | Some body -> ev_head st ls ev depth (beta_app st depth body args)
    | None -> c)
  | None -> c

(* [ev_whnf], then a literal's [Nat_double] unfolded, one level deeper each, until a constructor heads it. *)
and ev_ctor st ls ev depth c =
  let c = ev_whnf st ls ev depth c in
  if is_double st c then
    match Constr.kind c with
    | Constr.App (h, args) -> (
      match Constr.kind h with
      | Constr.Const (k, u) -> (
        match Option.bind (C.const_decl st.ch k) (C.def_body st.ch depth u) with
        | Some body -> ev_ctor st ls ev (depth + 1) (beta_app st depth body args)
        | None -> c)
      | _ -> c)
    | _ -> c
  else c

(* The closed Nat term [c] evaluated to a literal of the importer's form or a held operation: [ev_whnf], and the
   argument of each [Nat_succ] the same, one level deeper each. A literal (of the importer's form, read from
   [is_literal]'s memo when it was read before) is its own value and is returned as it is; a run of [Nat_succ]
   is walked in one loop, its base evaluated at the depth its last [Nat_succ] has, and the run rebuilt only when
   the base changed, so that no suffix of a run is asked whether it is a literal and no suffix goes through the
   round's memo. *)
and ev_nat st ls ev depth c =
  if is_literal st depth c then c
  else begin
    let c' = ev_whnf st ls ev depth c in
    if c' != c && is_literal st depth c' then c'
    else
      match Constr.kind c' with
      | Constr.App (h, [| x |]) when is_nat_succ st.refs h -> map_succ_run st depth c' h x (ev_nat st ls ev)
      | _ -> c'
  end

(* The normal form of the closed term [c]: [ev_whnf], then each relevant argument of a constructor after its
   parameters the same, one level deeper each; a Nat by [ev_nat]. A constructor's parameters, a proof argument,
   a lambda's body and anything under a binder stay as they are. *)
let rec ev_nf st ls ev depth c =
  let c = ev_whnf st ls ev depth c in
  match ctor_app c with
  | Some ((ind, _), _, _) when Ind.CanOrd.equal ind st.refs.nt_nat -> ev_nat st ls ev depth c
  | Some (cstr, h, args) ->
    let npar, rel = ctor_info st ls cstr in
    let n = Array.length args in
    if n <> npar + Array.length rel then c
    else begin
      C.tick st.ch n;
      Constr.mkApp
        (h, Array.mapi (fun i a -> if i >= npar && rel.(i - npar) then ev_nf st ls ev (depth + 1) a else a) args)
    end
  | None -> c

(* [c] with each held operation of [ops] (physically, wherever it stands: under binders, in a match's parameters
   and return predicate, a fixpoint's types and bodies, a constructor's parameters and proofs) replaced by
   [fill k n], [k] its index in [ops], [n] the binders above it. Each node visited charged, with one step for
   each operation it is compared with; a replacement is placed as it is (a literal or a [Rel]). *)
let fill_ops st depth ops c fill =
  let m = Array.length ops in
  let rec index c k =
    if k = m then -1
    else begin
      C.tick st.ch 1;
      if fst ops.(k) == c then k else index c (k + 1)
    end
  in
  let rec go depth n c =
    C.tick st.ch (C.node_steps c);
    C.check_depth depth;
    let k = index c 0 in
    if k >= 0 then fill k n else Constr.map_with_binders succ (go (depth + 1)) n c
  in
  go depth 0 c

(* [c] with each closed Nat operation [ev_head] would hold (an [Op] of a row or a [Div]), wherever it stands,
   replaced by the round's representative of its form and operand values ([held_rep]), so that the casts of
   [ec_proof] abstract every occurrence of one held operation in one form together. Each node charged; the
   closedness of an operation by [C.closed], tested at an operation only: tested at each node, it would read
   again each suffix of a unary literal's successor chain, which share one slot of its memo, so that a literal of
   [n] successors would cost about [n * n] steps. A literal of the importer's form holds no operation: it is
   returned as it is, read from [is_literal]'s memo once it has been read; a run of [Nat_succ] that is not one is
   walked in a loop, each suffix not asked again. *)
let rec ec_canon st ls ev depth c =
  match Constr.kind c with
  | Constr.App (h, [| x |]) when is_nat_succ st.refs h ->
    if is_literal st depth c then c else map_succ_run st depth c h x (ec_canon st ls ev)
  | _ ->
    C.tick st.ch (C.node_steps c);
    C.check_depth depth;
    let replaced =
      if not (Constr.isApp c) then None
      else
        match held_operands (nat_form st ls.ev_reader depth c) with
        | Some (z, a, b) when C.closed st.ch depth c -> canon_held st ls ev depth c z a b
        | Some _ | None -> None
    in
    (match replaced with Some r -> r | None -> Constr.map (ec_canon st ls ev (depth + 1)) c)

(* [c] = [f fa fb], of value function [z], held as [hold_op] holds it: when an operand or its value is [hold_min]
   or more or an operand is held (a representative of the round, [is_rep]); an operand that is a literal in
   another form ([OfNat.ofNat Nat 8 _]) or a small operation is no held operand, as [hold_op] evaluates both to
   literals. The representative of [f] on the operands' values, [c] itself when neither operand changes. *)
and canon_held st ls ev depth c z fa fb =
  let h, args = Constr.decompose_app c in
  match Constr.kind h with
  | Constr.Const (k, _) -> (
    let a = ec_canon st ls ev (depth + 1) fa in
    let b = ec_canon st ls ev (depth + 1) fb in
    match (value st ls.ev_reader depth a, value st ls.ev_reader depth b) with
    | Some va, Some vb -> (
      match z va vb with
      | Some v when (not (below_hold [ va; vb; v ])) || is_rep st ev a || is_rep st ev b ->
        let n = Array.length args in
        let f = if n = 2 then h else C.app_ch st.ch h (C.sub_ch st.ch args 0 (n - 2)) in
        let t = if a == fa && b == fb then c else C.app_ch st.ch f [| a; b |] in
        Some (held_rep st ev depth k f a b t va vb)
      | Some _ | None -> None)
    | _ -> None)
  | _ -> None

(* The universe level of the closed type [ty], its sort read by the bounded query ([C.type_of], then
   [C.expose_sort]): [Set], or the level of [Type@{l}]; [None] for any other sort, an algebraic universe, and a
   type whose sort the query does not read (a product, a sort). *)
let type_level st depth ty =
  match C.type_of st.ch st.ch.C.genv depth ty with
  | None -> None
  | Some s -> (
    match C.expose_sort st.ch st.ch.C.genv depth s with
    | Some Sorts.Set -> Some Univ.Level.set
    | Some (Sorts.Type u) -> Univ.Universe.level u
    | Some (Sorts.SProp | Sorts.Prop | Sorts.QSort _) | None -> None)

(* Whether two normal forms are the same value: [`Same] for the same term, two Nat literals of the same value
   (the ordinary reader), or the same constructor with the same parameters and the same relevant arguments
   (proofs are irrelevant); [`Differ] for different constructors of one type or different Nat values;
   [`Unknown] otherwise. Each node compared charged ([C.equal]), the values memoized. *)
let rec nf_compare st ls depth x y =
  C.tick st.ch 1;
  C.check_depth depth;
  if C.equal st.ch depth x y then `Same
  else
    match (value st st.nat depth x, value st st.nat depth y) with
    | Some a, Some b -> if Z.equal a b then `Same else `Differ
    | _ -> (
      match (ctor_app x, ctor_app y) with
      | Some (cx, _, ax), Some (cy, _, ay) ->
        if not (Construct.CanOrd.equal cx cy) then (if Ind.CanOrd.equal (fst cx) (fst cy) then `Differ else `Unknown)
        else
          let npar, rel = ctor_info st ls cx in
          let n = Array.length ax in
          if n <> Array.length ay || n <> npar + Array.length rel then `Unknown
          else
            let rec fields i r =
              if i = n then r
              else if i < npar then fields (i + 1) (if C.equal st.ch (depth + 1) ax.(i) ay.(i) then r else `Unknown)
              else if not rel.(i - npar) then fields (i + 1) r
              else
                match nf_compare st ls (depth + 1) ax.(i) ay.(i) with
                | `Same -> fields (i + 1) r
                | `Differ -> `Differ
                | `Unknown -> fields (i + 1) `Unknown
            in
            fields 0 `Same
      | _ -> `Unknown)

(* The tree size of the terms [cs] of the evaluation, each at a place of its own in a proof the pass builds, paid
   before the place is built: those terms share their subterms (the final normal form holds a literal at every
   place an operation of its value stood, and a motive's body one at every place of an earlier operation), so that
   a proof built of them may hold far more nodes as a tree, which the kernel walks, than the walks that made them
   charged. *)
let pay_trees st depth cs =
  C.pay st.ch
    (List.fold_left
       (fun acc c -> match acc with None -> None | Some _ -> C.add_size acc (C.size st.ch depth c))
       (Some 0) cs)

(* [e : x = y] at [ty] of level [level] turned into [y = x]: a fixed few nodes. *)
let eq_sym st ls ty level x y e =
  let nt = st.refs in
  let inst = inst1 level in
  C.tick st.ch 1;
  let eq = Constr.mkIndU (nt.nt_eq, inst) and refl = Constr.mkConstructU ((nt.nt_eq, 1), inst) in
  let motive = Constr.mkLambda (Context.nameR (Id.of_string "z"), ty, app eq [| ty; r1; x |]) in
  app (transport_any ls.lr level) [| ty; motive; x; y; e; app refl [| ty; x |] |]

(* A proof of [true = s] at Lean's [Bool] for a held [s], a [decide p inst] of value [true], through Lean's
   [decide_eq_true p inst proof]; [None] with no Lean [Bool] or no [decide_eq_true]. *)
let decide_lemma st ls s proof =
  match (Constr.kind s, ls.bool, ls.decide_thms) with
  | Constr.App (_, [| p; inst |]), Some (ind, blevel), k :: _ ->
    C.tick st.ch 1;
    let bty = Constr.mkIndU (ind, UVars.Instance.empty) in
    let tt = Constr.mkConstructU ((ind, 2), UVars.Instance.empty) in
    let e = app (Constr.mkConstU (k, UVars.Instance.empty)) [| p; inst; proof |] in
    Some (bty, blevel, eq_sym st ls bty blevel s tt e)
  | _ -> None

(* A proof of [N_0 = v] at [ty] (src/Lean.v's [eq] at [level]) from the rounds of a side ([ec_eval]); [None] when
   the lemma of a held operation is not generated (no certificate, no [decide_eq_true]); [Refused] when the kernel
   refuses one. Each motive's comparisons are charged before it is built ([fill_ops] charges its walk), and the tree
   size of [v] in [eq_refl] and of each motive's body and [v] before the place is built ([pay_trees]). *)
let ec_proof st ls depth ty level v rounds =
  let nt = st.refs in
  let inst = inst1 level in
  let eq = Constr.mkIndU (nt.nt_eq, inst) and refl = Constr.mkConstructU ((nt.nt_eq, 1), inst) in
  let step p (n, ops, lits) =
    let m = Array.length ops in
    (* [p : N[lits] = v]: each held operation cast back in, the later ones already, the earlier ones still at
       their literal *)
    let rec cast p j =
      if j < 0 then Some p
      else begin
        let s, hv = ops.(j) in
        let l = lits.(j) in
        C.tick st.ch m;
        let body =
          fill_ops st depth ops n (fun k b ->
              if k < j then lits.(k) else if k = j then Constr.mkRel (b + 1) else fst ops.(k))
        in
        match hv with
        | HNat _ -> (
          pay_trees st depth [ body; v ];
          match nat_lemma st ls.ev_reader depth l s with
          | None -> None
          | Some lemma ->
            let motive = Constr.mkLambda (Context.nameR (Id.of_string "z"), nat_type nt, app eq [| ty; body; v |]) in
            cast (app nt.nt_transport [| motive; l; s; lemma; p |]) (j - 1))
        | HDec proof -> (
          match decide_lemma st ls s proof with
          | None -> None
          | Some (bty, blevel, e) ->
            pay_trees st depth [ body; v ];
            let motive = Constr.mkLambda (Context.nameR (Id.of_string "z"), bty, app eq [| ty; body; v |]) in
            cast (app (transport_any ls.lr blevel) [| bty; motive; l; s; e; p |]) (j - 1))
      end
    in
    cast p (m - 1)
  in
  pay_trees st depth [ v ];
  List.fold_right (fun r acc -> Option.bind acc (fun p -> step p r)) rounds (Some (app refl [| ty; v |]))

let head_is_ind c = Constr.isInd (fst (Constr.decompose_app c))

let is_nonneg ls ind = match ls.nonneg with Some i -> Ind.CanOrd.equal i ind | None -> false

(* Whether [k] applied to [args] is Lean's [Dvd.dvd Nat Nat.instDvd a b]; each comparison charged. *)
let is_nat_dvd st ls k args =
  Array.length args = 4 && mem_const st k ls.dvds && is_nat_ind st.refs args.(0)
  && match Constr.kind args.(1) with Constr.Const (i, _) -> mem_const st i ls.instdvds | _ -> false

(* A proof of [a ∣ b] at Nat ([args] those of Lean's [Dvd.dvd Nat Nat.instDvd a b], [a] positive), by the
   evaluator's reader: [Exists.intro] with the witness [b / a] and a Nat lemma, the proposition reduced
   ([reduced ()]) to Lean's [Exists]. *)
let dvd_proof st ls depth args reduced =
  match (value st ls.ev_reader depth args.(2), value st ls.ev_reader depth args.(3)) with
  | Some a, Some b when Z.sign a > 0 && Z.equal (Z.rem b a) Z.zero -> (
    match reduced () with
    | Some (eh, [| ety; epred |]) -> (
      match Constr.kind eh with
      | Constr.Ind (ind, u) -> (
        let c = nat_lit st (Z.div b a) in
        match Constr.decompose_app (beta_app st depth epred [| c |]) with
        | _, [| _; x; y |] ->
          Option.map
            (fun e -> app (Constr.mkConstructU ((ind, 1), u)) [| ety; epred; c; e |])
            (nat_lemma st ls.ev_reader depth x y)
        | _ -> None)
      | _ -> None)
    | Some _ | None -> None)
  | _ -> None

(* A proof of src/Lean.v's [Nat_le x y] by the evaluator's reader's certificates ([le_of_toN]). *)
let le_proof st ls depth x y =
  match (certify st ls.ev_reader depth x, certify st ls.ev_reader depth y) with
  | Some (vx, px, _), Some (vy, py, _) when Z.leq vx vy ->
    Some (le_of_toN st ls.lr x y (n_literal st.refs vx) (n_literal st.refs vy) px py)
  | _ -> None

(* The held operations of the normal form [c] that [ec_eval] replaces: each maximal closed application of a held
   function, held [decide] or representative of a class function's form ([ev_reps]), whose value [held_value]
   gives, anywhere in [c] (under binders, in parameters, types and proofs too); a held function applied to two
   operands only as [canon_held] holds it (an operand or the value [hold_min] or more, or an operand a
   representative), so that a small one in a parameter, a proof or a type ([Nat.pow 2 8] in a [Fin]'s bound and its
   [decide] proof) is not abstracted by a motive that holds it where the kernel needs its value. [Eval_stop] at a
   valued [Nat.mod], however small (no certificate proves its value). Each node charged, closedness by [C.closed],
   one step for each operation or representative an occurrence is compared with. *)
let rec held_ops st ls ev depth c =
  let acc = ref [] in
  let rec walk depth c =
    match Constr.kind c with
    | Constr.App (h, [| x |]) when is_nat_succ st.refs h ->
      (* a literal of the importer's form holds no operation *)
      if not (is_literal st depth c) then
        ignore
          (map_succ_run st depth c h x (fun depth b ->
               walk depth b;
               b))
    | _ -> walk_node depth c
  and walk_node depth c =
    C.tick st.ch (C.node_steps c);
    C.check_depth depth;
    let h, args = Constr.decompose_app c in
    let candidate =
      match Constr.kind h with
      | Constr.Const (k, _) ->
        (Array.length args = 2 && (mem_const st k ls.held || is_held_decide st ls depth c)
        || (Array.length args > 2 && is_rep st ev c))
        && C.closed st.ch depth c
      | _ -> false
    in
    if candidate then
      match held_value st ls ev depth c with
      | Some _ when (match Constr.kind h with Constr.Const (k, _) -> is_mod st k | _ -> false) ->
        raise Eval_stop
      | Some (_, small) when small () -> Array.iter (walk (depth + 1)) args
      | Some (v, _) ->
        if
          not
            (List.exists
               (fun (c', _) ->
                 C.tick st.ch 1;
                 c' == c)
               !acc)
        then acc := (c, v) :: !acc
      | None -> Array.iter (walk (depth + 1)) args
    else Constr.iter (walk (depth + 1)) c
  in
  walk depth c;
  Array.of_list (List.rev !acc)

(* The value of [c], a held operation, by the evaluator's reader, or [true] with a proof of a [decide]'s
   proposition ([prove_prop]); with it, whether [c] is a held function on two operands that [canon_held] would not
   hold (the operands and the value below [hold_min], neither operand a representative), its operands compared with
   the representatives only when asked. *)
and held_value st ls ev depth c =
  let never () = false in
  match Constr.kind c with
  | Constr.App (h, [| a; b |]) -> (
    match Constr.kind h with
    | Constr.Const (k, _) when mem_const st k ls.decides ->
      Option.map (fun pr -> (HDec pr, never)) (prove_prop st ls (depth + 1) a)
    | Constr.Const (k, _) -> (
      match (value st ls.ev_reader (depth + 1) a, value st ls.ev_reader (depth + 1) b) with
      | Some va, Some vb ->
        Option.map
          (fun v -> (HNat v, fun () -> below_hold [ va; vb; v ] && not (is_rep st ev a || is_rep st ev b)))
          (op_value st ls k va vb)
      | _ -> None)
    | _ -> None)
  | Constr.App _ -> Option.map (fun v -> (HNat v, never)) (value st ls.ev_reader depth c)
  | _ -> None

(* The rounds of [t]: the normal forms [N_0], ..., [N_K], the held operations of each and the terms put in their
   place (none in [N_K], the value). Each round starts with an empty memo, table and wait ([new_round]).
   [Eval_stop] after [max_rounds] replacement rounds, and when [N_K] has no held operation but its round still
   waits (on one no round gives a value). *)
and ec_eval st ls ev depth t =
  let rec round t k acc =
    if k > max_rounds then raise Eval_stop
    else begin
      new_round ev;
      let n = ec_canon st ls ev depth (ev_nf st ls ev depth t) in
      let ops = held_ops st ls ev depth n in
      if Array.length ops = 0 then (if ev.ev_wait then raise Eval_stop else (n, List.rev acc))
      else begin
        C.tick st.ch (Array.length ops);
        let lits =
          Array.map
            (fun (_, v) ->
              match v with
              | HNat v -> nat_lit st v
              | HDec _ -> ( match bool_ctor ls true with Some t -> t | None -> raise Eval_stop))
            ops
        in
        round (fill_ops st depth ops n (fun k _ -> lits.(k))) (k + 1) ((n, ops, lits) :: acc)
      end
    end
  in
  round t 0 []

(* A proof of [a = d] at [ty] (level [level]) by [ec_eval] and [ec_proof] of each side: [`Proof p]; [`Differ]
   when their values differ; [`Nothing_held] when the evaluation held no operation, or held operations only at
   positions it does not evaluate (a constructor's parameters, proofs, types, a match's return predicate): the
   kernel converts the two terms as without the pass, whereas a lemma abstracting only such an operation may
   have a motive the kernel refuses only after computing it ([RLI434S.stop_opaque]'s bound [2 ^ 32] did not
   end within 10 s); [`Capped] when an outer pair needs more than [pair_cap]; [`No] otherwise (an [Eval_stop],
   [`Unknown], a sub-lemma not generated). An outer pair runs in [C.with_pair] (the cap's one handler, its
   [C.Out_of_pair] giving [`Capped]); a nested one, from [prove_prop], runs inside the outer pair, whose cap counts
   its charges. *)
and ec_eq_proof st ls depth ty level a d =
  let pair () =
    let ev = new_ev () in
    match
      let ea = ec_eval st ls ev depth a in
      (ea, ec_eval st ls ev depth d)
    with
    | exception Eval_stop -> if ev.ev_held then `No else `Nothing_held
    | (_, []), (_, []) -> `Nothing_held
    | _ when not ev.ev_held_eval -> `Nothing_held
    | (na, ra), (nd, rd) -> (
      match nf_compare st ls depth na nd with
      | `Differ -> `Differ
      | `Unknown -> `No
      | `Same -> (
        match ec_proof st ls depth ty level na ra with
        | None -> `No
        | Some pa -> (
          match ec_proof st ls depth ty level nd rd with
          | None -> `No
          | Some pd ->
            (* [pa : a = na], [pd : d = nd], so [nd = d], then [a = d]: [nd] at two places *)
            pay_trees st depth [ nd; nd ];
            let eq = Constr.mkIndU (st.refs.nt_eq, inst1 level) in
            let motive = Constr.mkLambda (Context.nameR (Id.of_string "z"), ty, app eq [| ty; a; r1 |]) in
            `Proof (app (transport_any ls.lr level) [| ty; motive; nd; d; eq_sym st ls ty level d nd pd; pa |]))))
  in
  match C.with_pair st.ch pair_cap pair with Some r -> r | None -> `Capped

(* A proof of the closed proposition [p], or [None]: [a ∣ b] at Nat ([Dvd.dvd Nat Nat.instDvd], [a > 0])
   through [Exists.intro] with the witness [b / a] and a Nat lemma; otherwise [p] reduced at its head ([C.whd]
   from a count of 0, at most [C.max_head_steps] steps, stopping at an inductive type) to src/Lean.v's
   [Nat_le x y] ([Nat_le_of_toN]), [eq] at Nat (a Nat lemma), [eq] at another data type (a nested
   [ec_eq_proof]), or Lean's [Int.NonNeg x] ([nonneg_proof]). It proves the value of a held [decide]: each value
   and certificate is the evaluator's reader's. *)
and prove_prop st ls depth p =
  C.tick st.ch 1;
  C.check_depth depth;
  let nt = st.refs in
  let h, args = Constr.decompose_app p in
  let reduced () =
    match C.whd ~stop:head_is_ind st.ch st.ch.C.genv (depth + 1) 0 p with
    | Some (_, rh, rargs) -> Some (rh, rargs)
    | None -> None
  in
  match Constr.kind h with
  | Constr.Const (k, _) when is_nat_dvd st ls k args -> dvd_proof st ls depth args reduced
  | _ -> (
    match reduced () with
    | None -> None
    | Some (rh, rargs) -> (
      match Constr.kind rh with
      | Constr.Ind (ind, _) when Ind.CanOrd.equal ind ls.lr.lr_nat_le && Array.length rargs = 2 ->
        le_proof st ls depth rargs.(0) rargs.(1)
      | Constr.Ind (ind, _) when Ind.CanOrd.equal ind nt.nt_eq && Array.length rargs = 3 -> (
        if is_nat_ind nt rargs.(0) then nat_lemma st ls.ev_reader depth rargs.(1) rargs.(2)
        else
          match type_level st depth rargs.(0) with
          | Some level when C.closed st.ch depth rargs.(0) -> (
            match ec_eq_proof st ls (depth + 1) rargs.(0) level rargs.(1) rargs.(2) with
            | `Proof pr -> Some pr
            | `Differ | `No | `Nothing_held | `Capped -> None)
          | Some _ | None -> None)
      | Constr.Ind (ind, u) when is_nonneg ls ind && Array.length rargs = 1 -> nonneg_proof st ls depth ind u rargs.(0)
      | _ -> None))

(* Lean's [Int.NonNeg x]: [x] evaluated (a nested evaluation) to [Int.ofNat k]; [Int.NonNeg.mk k], of type
   [NonNeg (Int.ofNat k)], cast along the nested proof of [Int.ofNat k = x]; the nested normal form and its [k]
   paid at their places. *)
and nonneg_proof st ls depth ind u x =
  match ec_eval st ls (new_ev ()) (depth + 1) x with
  | exception Eval_stop -> None
  | nx, _ -> (
    match ctor_app nx with
    | Some ((_, 1), _, [| k |]) -> (
      let typed =
        Option.bind (C.type_of st.ch st.ch.C.genv depth x) (fun ity ->
            Option.map (fun l -> (ity, l)) (type_level st depth ity))
      in
      match typed with
      | None -> None
      | Some (ity, level) -> (
        match ec_eq_proof st ls (depth + 1) ity level nx x with
        | `Proof e ->
          pay_trees st depth [ nx; k ];
          let mk = app (Constr.mkConstructU ((ind, 1), u)) [| k |] in
          let motive = Constr.mkLambda (Context.nameR (Id.of_string "z"), ity, app (Constr.mkIndU (ind, u)) [| r1 |]) in
          Some (app (transport_any ls.lr level) [| ity; motive; nx; x; e; mk |])
        | `Nothing_held ->
          pay_trees st depth [ k ];
          Some (app (Constr.mkConstructU ((ind, 1), u)) [| k |])
        | `Differ | `No | `Capped -> None))
    | _ -> None)

(* The rule of literal arithmetic (README, "Transport of proof arguments across Nat literals"): [a] (in the
   argument's type) and [d] (in the expected type), closed, with different heads (two constants, two constructors,
   or one of each), of a closed type [ty] whose level [type_level] reads, are a [Val_hole] when [ec_eq_proof]
   proves [a = d]; [`Capped] when their pair needs more than [pair_cap]. [`No_hole] in every other case, two
   different values included: the kernel converts the two terms, or refuses the argument, as without the pass,
   and the pass looks inside them as before. *)
let ec_hole st ls depth a d =
  let heads_differ =
    match (Constr.kind (fst (Constr.decompose_app a)), Constr.kind (fst (Constr.decompose_app d))) with
    | Constr.Const (ka, _), Constr.Const (kd, _) -> not (Constant.CanOrd.equal ka kd)
    | Constr.Construct (ca, _), Constr.Construct (cd, _) -> not (Construct.CanOrd.equal ca cd)
    | (Constr.Const _ | Constr.Construct _), (Constr.Const _ | Constr.Construct _) -> true
    | _ -> false
  in
  if not (heads_differ && C.closed st.ch depth a && C.closed st.ch depth d) then `No_hole
  else
    match C.type_of st.ch st.ch.C.genv depth a with
    | None -> `No_hole
    | Some ty -> (
      match type_level st depth ty with
      | Some level when C.closed st.ch depth ty -> (
        match ec_eq_proof st ls depth ty level a d with
        | `Proof proof ->
          let vcast = transport_any ls.lr level in
          `Hole (Val_hole { va = a; vd = d; vty = ty; vlevel = level; vproof = proof; vcast })
        | `Capped -> `Capped
        | `Differ | `No | `Nothing_held -> `No_hole)
      | Some _ | None -> `No_hole)

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
   same literal as [x], and the places of [fin_hole] and [ec_hole]. [depth] is the nesting of the place the types
   come from. A hole equal to an earlier one is that one; each earlier hole compared is charged. Below a pair that
   [ec_hole] declined at the cap no node pair is evaluated (each evaluation would read again subterms the declined
   pair's evaluation read, at up to [pair_cap] steps each); the Nat and Fin holes there are found as before. *)
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
    match (value st st.nat depth a, value st st.nat depth d) with
    | None, _ | _, None -> None
    | Some va, Some vd ->
      if not (Z.equal va vd) then raise Other_values
      else if Z.lt va transport_min || C.equal st.ch depth a d then Some Keep
      else
        match (literal_of st depth a, literal_of st depth d) with
        | Some la, Some ld when C.equal st.ch depth la ld -> Some Keep
        | _ -> Some (add depth (Nat_hole (a, d)))
  in
  let rec go depth capped a d =
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
      match (match st.l with Some ls when not capped -> ec_hole st ls depth a d | Some _ | None -> `No_hole) with
      | `Hole h -> add depth h
      | (`Capped | `No_hole) as r ->
        let go = go (depth + 1) (capped || r = `Capped) in
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
  let shape = go depth false a d in
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
   type ends in a record of one field, or [OfNat.ofNat] at such a record. The Nat case's is [has_nat_from]. *)
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
  if not (has_nat_from st transport_min depth dom || has_fin_site st depth dom) then None
  else
    match Option.map (fun ty -> nat_diff st depth (C.beta st.ch depth ty) dom) (C.type_of st.ch env depth arg) with
    | exception (Other_values | Refused) -> None
    | None | Some (_, [||]) -> None
    | Some (shape, holes) -> (
      match
        Array.map
          (function
            | Nat_hole (x, y) -> eq_lemma st depth x y (nat_eq_proof st st.nat depth x y)
            | Fin_hole { sa; sd; fv; _ } -> eq_lemma st depth sa.fval sd.fval (fin_eq_proof st sa.fval sd.fval fv)
            | Val_hole { va; vd; vty; vlevel; vproof; _ } ->
              eq_lemma_at st depth vty vlevel va vd (fun () -> Some vproof))
          holes
      with
      | exception Refused -> None
      | lemmas ->
      if Array.exists Option.is_empty lemmas then None
      else begin
        let nt = st.refs in
        (* [dom] under the motive's one or two binders, lifted once each for all the holes. *)
        let dom1 = lazy (C.lift_ch st.ch depth 1 dom) and dom2 = lazy (C.lift_ch st.ch depth 2 dom) in
        let side k j = if j < k then snd (hole_terms holes.(j)) else fst (hole_terms holes.(j)) in
        let cast p k hole =
          C.tick st.ch 1;
          let lemma = Constr.mkConstU (Option.get lemmas.(k), UVars.Instance.empty) in
          (* the cast [head pre motive x y lemma p], the motive over [bty] *)
          let along head pre bty x y =
            let body =
              nat_fill st shape (Lazy.force dom1) 0 (fun j depth -> if j = k then Constr.mkRel (depth + 1) else side k j)
            in
            app head (Array.append pre [| Constr.mkLambda (Context.anonR, bty, body); x; y; lemma; p |])
          in
          match hole with
          | Nat_hole (x, y) -> along nt.nt_transport [||] (nat_type nt) x y
          | Val_hole { va; vd; vty; vcast; _ } -> along vcast [| vty |] vty va vd
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
      end)

(* Whether [f] applied to [args] is [Nat_succ] or [Nat_double] applied to one argument, whose declared types
   [setup] has read once to be one relevant Nat argument to Nat: such an application has no SProp argument, so
   [transport_walk] reads no type for it and peels no product. *)
let unary_nat_head st f args =
  Array.length args = 1
  && ((st.unary_succ && is_nat_succ st.refs f) || (st.unary_double && is_double_head st.refs f))

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

(* [c] at the nesting [depth] under [env], each SProp argument of an application transported where it needs it
   ([transport_args]), one step per node. An application of [Nat_succ] or [Nat_double] has none: a literal of the
   importer's form holds no other node, so it is the same term after the walk and is returned as it is, for the
   steps of [walk_literal] (one at a hit of its memo), not those of its chain at each place, whatever the binders
   above it; a run of [Nat_succ] that is no literal is walked in one loop to its base ([map_succ_run]), so that no
   suffix of the run is asked again whether it is a literal. *)
let rec transport_walk st env depth c =
  C.tick st.ch 1;
  C.check_depth depth;
  let walk env = transport_walk st env (depth + 1) in
  let push d = Environ.push_rel d env in
  match Constr.kind c with
  | Constr.App (f, args) when unary_nat_head st f args ->
    if walk_literal st depth c then c
    else if is_nat_succ st.refs f then map_succ_run st depth c f args.(0) (transport_walk st env)
    else
      let x = walk env args.(0) in
      if x == args.(0) then c else C.app_ch st.ch f [| x |]
  | Constr.App (f, args) ->
    let f' = walk env f in
    let args' = transport_args st env depth f' (C.smart_map_ch st.ch (walk env) args) in
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
      (has_nat_from st transport_min depth ty || has_fin_site st depth ty)
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
      match value st st.nat depth c with Some v -> Z.geq v transport_min | None -> false)
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

(* Literal arithmetic's view of the export at one entry, when [l_refs ()] is [Some] (in [setup], inside the stop
   handler of [transport], each read charged): 9 fixed names more; the constants of the Fin case's rows of
   [sub_names] and [div_names] (found by those very names) for the [Sub] row and the [Div] form; Lean's [Bool]
   (the inductive type that ends [Decidable.decide]'s declared type, each product peeled one step, its level read
   from its arity); Lean's [Int.NonNeg] (the inductive type that heads [Int.le]'s body, each lambda peeled one
   step); and the function without universes of [Nat.pred] with its [toN_pred] proof. Each read that fails gives
   [None], never an exception. *)
let setup_l ctx ch nt lr rows fin_ops mod_op =
  let fin_row names = (List.find (fun row -> row.fin_spec.fin_names == names) fin_ops).fin_op_consts in
  let ev_rows = List.map (fun spec -> { spec; op_consts = fin_row spec.names }) ev_op_specs in
  let divs = fin_row div_names in
  let pred =
    Option.map
      (fun k ->
        let pred = Constr.mkConstU (k, UVars.Instance.empty) in
        (pred, app lr.lr_pred [| pred; refl_nat nt (nat_zero nt); lam1 nt (refl_nat nt r1) |]))
      (List.find_opt (mono_const ch) (consts ctx ch [ "Nat"; "pred" ]))
  in
  let div_thms = consts ctx ch [ "Nat"; "div_eq_of_lt_le" ] in
  let beqs = consts ctx ch [ "Nat"; "beq" ] in
  let bles = consts ctx ch [ "Nat"; "ble" ] in
  let decides = consts ctx ch [ "Decidable"; "decide" ] in
  let decide_thms = consts ctx ch [ "decide_eq_true" ] in
  let dvds = consts ctx ch [ "Dvd"; "dvd" ] in
  let instdvds = consts ctx ch [ "Nat"; "instDvd" ] in
  let int_les = consts ctx ch [ "Int"; "le" ] in
  let rec under_prods depth ty =
    C.tick ch 1;
    C.check_depth depth;
    match Constr.kind ty with Constr.Prod (_, _, b) -> under_prods (depth + 1) b | _ -> ty
  in
  let rec under_lambdas depth c =
    C.tick ch 1;
    C.check_depth depth;
    match Constr.kind c with Constr.Lambda (_, _, b) -> under_lambdas (depth + 1) b | _ -> c
  in
  let head_ind c = match Constr.kind (fst (Constr.decompose_app c)) with Constr.Ind (ind, _) -> Some ind | _ -> None in
  let bool =
    List.find_map
      (fun k ->
        match Option.bind (C.const_decl ch k) (fun cb -> head_ind (under_prods 0 cb.Declarations.const_type)) with
        | None -> None
        | Some ind -> (
          match Option.map Constr.kind (C.ind_type ch 0 ind UVars.Instance.empty) with
          | Some (Constr.Sort Sorts.Set) -> Some (ind, Univ.Level.set)
          | Some (Constr.Sort (Sorts.Type u)) -> Option.map (fun l -> (ind, l)) (Univ.Universe.level u)
          | Some _ | None -> None))
      decides
  in
  let nonneg =
    List.find_map
      (fun k ->
        match C.const_decl ch k with
        | Some cb -> Option.bind (C.def_body ch 0 UVars.Instance.empty cb) (fun b -> head_ind (under_lambdas 0 b))
        | None -> None)
      int_les
  in
  let all_rows = rows @ ev_rows in
  {
    lr;
    ev_reader = nat_reader all_rows (Some { div_op = divs; div_thms; div_lr = lr });
    divs;
    held = List.concat_map (fun row -> row.op_consts.funs) all_rows @ divs.funs @ mod_op.funs;
    beqs;
    bles;
    decides;
    decide_thms;
    dvds;
    instdvds;
    bool;
    nonneg;
    pred;
    ctors = C.constructor_table ();
  }

(* The pass at the entry [entry]: the entry's view of the export, read once and charged as the rest of its part
   (the rows' constants, the constants of the Fin case and its rows, the declared types of [Nat_succ] and
   [Nat_double], see [unary_nat_head], and literal arithmetic's view when [lrefs] is [Some]), and empty memos. *)
let setup ctx refs lrefs ch entry =
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
  let l = Option.map (fun lr -> setup_l ctx ch refs lr rows fin_ops mod_op) lrefs in
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
    l;
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
    nat = nat_reader rows None;
    fin_reader = { ceiling = fin_ceiling; divisor_by_value = true; rmemo = C.memo (); rconsts = C.constant_table () };
    param_reader =
      { ceiling = param_ceiling; divisor_by_value = false; rmemo = C.memo (); rconsts = C.constant_table () };
    nat_lits = C.value_table ();
    lit_memo = C.memo ();
    walk_memo = C.memo ();
    walk_lits = Array.make walk_lits_max Constr.mkProp;
    walk_lits_n = 0;
    next = 0;
    count = 0;
    lemmas = [];
    lemma_ids = C.id_table ();
  }

let transport ctx env ~entry ty body =
  match refs () with
  | Some refs when registered op_specs -> (
    let lrefs = l_refs () in
    let ch = C.create env ~steps:(budget ()) ~total:(total_budget ()) in
    match
      let st = setup ctx refs lrefs ch entry in
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
