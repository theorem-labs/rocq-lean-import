(* Transport of SProp arguments across closed Nat terms of equal value (see the .mli and README, "Transport
   of proof arguments across Nat literals"). The values this module computes with OCaml's Z are not trusted:
   they only find the places to transport. Each place gets a lemma [x = y] whose proof goes through Rocq's
   binary [N] (the lemmas after [toN] in src/Lean.v), and the kernel checks it; a wrong value gives a lemma
   the kernel refuses. *)

open Names

type context = {
  consts : string list -> Constant.t list;
  declare : Id.t -> Constr.types -> Constr.t -> GlobRef.t;
  log : Pp.t -> unit;
}

type transported = { value : Constr.t; count : int; lemmas : Id.t list }

(* The smallest value worth a lemma: the kernel compares smaller ones unit by unit quickly enough. *)
let transport_min = Z.of_int 4096

(* The largest value, in bits, the finder computes: a certificate checks binary arithmetic on it. *)
let max_bits = 1024

(* A certificate of a literal below this value is [Logic.eq_refl]: the kernel computes [toN] of it. *)
let small_literal = Z.of_int 8192

(* The budget charges the scans, Nat recognition and certificate construction. A reused certificate
   costs its full number of steps again: the kernel checks the expanded proof tree. *)
let budget = 1_000_000

(* The deepest nesting the pass follows: the Nat terms the finder computes, and the terms its scans and walks
   go through, counted together from the entry's value or type down. Deeper, the pass stops ([Out_of_budget])
   before its recursion can exhaust the stack. *)
let max_depth = 10_000

exception Out_of_budget

let check_depth depth = if depth > max_depth then raise Out_of_budget

(* What the pass uses from src/Lean.v and Corelib. *)
type refs = {
  nt_nat : inductive;
  nt_double : Constant.t;
  nt_eq : inductive;
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
    match (lib_ref "lean.Nat", lib_ref "lean.Nat_double", lib_ref "lean.Eq") with
    | GlobRef.IndRef nt_nat, GlobRef.ConstRef nt_double, GlobRef.IndRef nt_eq ->
      Some
        {
          nt_nat;
          nt_double;
          nt_eq;
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

(* The binary literal of [v] (Rocq's [N]). *)
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

(* Memo tables keyed by the term itself (physical equality). *)
module PH = Hashtbl.Make (struct
  type t = Constr.t

  let equal = ( == )
  let hash = Hashtbl.hash
end)

type state = {
  ctx : context;
  refs : refs;
  genv : Environ.env;
  sigma : Evd.evar_map;
  rows : op_row list;
  of_nat : Constant.t list;
  inst_of_nat : Constant.t list;
  triggers : Constant.t list;  (** the constants that may make an entry need the pass *)
  lemma_of : nat_op -> (Constr.t * Constr.t) option;
  entry : Id.t;
  mutable steps : int;
  values : Z.t option PH.t;
  mutable const_values : Z.t option Cmap_env.t;
  certs : (Z.t * Constr.t * int) option PH.t;
  mutable const_certs : (Z.t * Constr.t * int) option Cmap_env.t;
  mutable next : int;  (** the number of the next lemma this entry generates *)
  mutable count : int;  (** arguments transported *)
  mutable lemmas : Id.t list;  (** the lemmas they use, last first *)
}

let tick st n =
  st.steps <- st.steps - n;
  if st.steps < 0 then raise Out_of_budget

let mem_const c l = List.exists (Constant.CanOrd.equal c) l

let is_nat_ind st c =
  match Constr.kind c with Constr.Ind (ind, _) -> Ind.CanOrd.equal ind st.refs.nt_nat | _ -> false

let rec pat_matches st p c =
  match p with
  | Nat_type -> is_nat_ind st c
  | Any -> true
  | Inst (ks, ps) ->
    let h, args = Constr.decompose_app c in
    (match Constr.kind h with
    | Constr.Const (k, _) ->
      mem_const k ks && Array.length args = List.length ps
      && List.for_all2 (pat_matches st) ps (Array.to_list args)
    | _ -> false)

(* The body of the constant [cu] when it is a transparent constant of type Nat. *)
let nat_const_body st ((c, _) as cu) =
  match Environ.lookup_constant_opt c st.genv with
  | Some cb
    when is_nat_ind st cb.Declarations.const_type && Declareops.constant_has_body cb
         && not (Declareops.is_opaque cb) ->
    Environ.constant_opt_value_in st.genv cu
  | _ -> None

(* The one recognizer of the Nat forms: every guard is here. *)
let nat_form st c =
  let h, args = Constr.decompose_app c in
  let nargs = Array.length args in
  match Constr.kind h with
  | Constr.Construct ((ind, 1), _) when nargs = 0 && Ind.CanOrd.equal ind st.refs.nt_nat -> Some Zero
  | Constr.Construct ((ind, 2), _) when nargs = 1 && Ind.CanOrd.equal ind st.refs.nt_nat -> Some (Succ args.(0))
  | Constr.Const (k, _) when nargs = 1 && Constant.CanOrd.equal k st.refs.nt_double -> Some (Double args.(0))
  | Constr.Const cu when nargs = 0 -> Option.map (fun b -> Unfold b) (nat_const_body st cu)
  | Constr.Const (k, _)
    when nargs = 3 && mem_const k st.of_nat && is_nat_ind st args.(0)
         && pat_matches st (Inst (st.inst_of_nat, [ Any ])) args.(2) ->
    Some (Unfold (snd (Constr.decompose_app args.(2))).(0))
  | Constr.Const (k, _) when nargs = 6 ->
    List.find_map
      (fun row ->
        if mem_const k row.classes && is_nat_ind st args.(0) && is_nat_ind st args.(1)
           && is_nat_ind st args.(2) && pat_matches st row.inst_pat args.(3)
        then Some (Op (row, Constr.mkApp (h, Array.sub args 0 4), args.(4), args.(5)))
        else None)
      st.rows
  | Constr.Const (k, _) when nargs = 2 ->
    List.find_map
      (fun row -> if mem_const k row.funs then Some (Op (row, h, args.(0), args.(1))) else None)
      st.rows
  | _ -> None

(* [find] and [add] of the memo of [c]: its constant's when it is a constant without universe instance,
   else its own. *)
let memo st phys consts set c =
  match Constr.kind c with
  | Constr.Const (k, u) when UVars.Instance.is_empty u ->
    ((fun () -> Cmap_env.find_opt k (consts st)), fun v -> set st (Cmap_env.add k v (consts st)))
  | _ -> ((fun () -> PH.find_opt phys c), fun v -> PH.replace phys c v)

(* The value of the closed Nat term [c], each term (or constant) computed once per entry. *)
let rec value st depth c =
  let find, add =
    memo st st.values (fun st -> st.const_values) (fun st m -> st.const_values <- m) c
  in
  match find () with
  | Some v -> v
  | None ->
    let v = compute st depth c in
    add v;
    v

and compute st depth c =
  tick st 1;
  check_depth depth;
  match nat_form st c with
  | None -> None
  | Some f ->
    let value = value st (depth + 1) in
    (match f with
    | Zero -> Some Z.zero
    | Succ m -> Option.bind (value m) (fun v -> bounded (Z.succ v))
    | Double m -> Option.bind (value m) (fun v -> bounded (Z.shift_left v 1))
    | Unfold b -> value b
    | Op (row, _, a, b) ->
      (match (value a, value b) with Some x, Some y -> row.spec.z x y | _ -> None))

(* Whether [c] is a literal of the importer's form. *)
let rec is_literal st depth c =
  check_depth depth;
  match nat_form st c with
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
    match nat_form st c with
    | Some (Unfold b) ->
      tick st 1;
      literal_of st (depth + 1) b
    | Some (Zero | Succ _ | Double _ | Op _) | None -> None

(* The value [v] of [t], a proof of [Logic.eq (toN t) w] for [w] the binary literal of [v], and the size of
   that proof; [None] when [t] has no value or an operation it needs has no [toN] lemma. Every step states
   its own term, so that the kernel only compares a term with itself, and checks each binary operation on
   literals. A proof built once is used again, its size counted again. *)
let rec certify st depth t =
  let find, add = memo st st.certs (fun st -> st.const_certs) (fun st m -> st.const_certs <- m) t in
  match find () with
  | Some r ->
    Option.iter (fun (_, _, size) -> tick st size) r;
    r
  | None ->
    let r = certify_node st depth t in
    add r;
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
      let sub = certify st (depth + 1) in
      let step lemma m =
        Option.map
          (fun (vm, pm, sm) -> (v, app lemma [| m; n_literal nt vm; w; pm; refl_n nt w |], sm + 1))
          (sub m)
      in
      (match nat_form st t with
      | Some Zero -> Some (v, refl_n nt w, 1)
      | Some (Succ m) -> step nt.nt_succ_step m
      | Some (Double m) -> step nt.nt_double_step m
      | Some (Unfold b) ->
        Option.map (fun (_, pb, sb) -> (v, app nt.nt_unfold_step [| t; b; w; refl_nat nt t; pb |], sb + 1)) (sub b)
      | Some (Op (row, f, a, b)) ->
        (match (st.lemma_of row.spec.op, sub a, sub b) with
        | Some (g, hg), Some (va, pa, sa), Some (vb, pb, sb) ->
          let hfg = lam2 nt (refl_nat nt (app (Vars.lift 2 f) [| r2; r1 |])) in
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

(* The lemma [x = y] for two closed Nat terms of equal value, generated and declared on first use, at the
   nesting [depth] of the place that needs it. A lemma the kernel refuses is logged and not used. *)
let nat_eq_lemma st depth x y =
  match List.find_opt (fun ((x', y'), _) -> Constr.equal x x' && Constr.equal y y') !lemma_cache with
  | Some (_, c) -> Some c
  | None ->
    let nt = st.refs in
    let levels = Vars.universes_of_constr ~init:(Vars.universes_of_constr x) y in
    if not (Vars.closed0 x && Vars.closed0 y)
       || Result.is_error (UGraph.check_declared_universes (Global.universes ()) levels)
    then None
    else
      match (certify st depth x, certify st depth y) with
      | Some (vx, cx, _), Some (vy, cy, _) when Z.equal vx vy ->
        let eq = Constr.mkIndU (nt.nt_eq, UVars.Instance.of_array ([||], [| Univ.Level.set |])) in
        let ty = app eq [| nat_type nt; x; y |] in
        let proof = app nt.nt_nat_eq [| x; y; n_literal nt vx; cx; cy |] in
        st.next <- st.next + 1;
        let id = Id.of_string (Id.to_string st.entry ^ "__nat_eq_" ^ string_of_int st.next) in
        let id =
          if Global.exists_objlabel id then Namegen.next_global_ident_away (Global.safe_env ()) id Id.Set.empty
          else id
        in
        (match st.ctx.declare id ty proof with
        | GlobRef.ConstRef c ->
          lemma_cache := ((x, y), c) :: !lemma_cache;
          Some c
        | GlobRef.VarRef _ | GlobRef.IndRef _ | GlobRef.ConstructRef _ -> assert false
        | exception e when CErrors.noncritical e ->
          let env = Global.env () in
          let pr = Printer.pr_constr_env env (Evd.from_env env) in
          st.ctx.log
            Pp.(
              str "the generated lemma " ++ Id.print id ++ str " : " ++ pr x ++ str " = " ++ pr y
              ++ str " is refused by the kernel: " ++ CErrors.print e);
          None)
      | _ -> None

(* Where two types differ: [Keep] takes the expected type's subterm (a difference there is the kernel's to
   convert, as without the pass), [Hole k] the [k]th pair of closed Nat terms of equal value. *)
type nat_shape =
  | Keep
  | Hole of int
  | App_s of nat_shape * nat_shape array
  | Prod_s of nat_shape * nat_shape
  | Lambda_s of nat_shape * nat_shape
  | LetIn_s of nat_shape * nat_shape * nat_shape
  | Proj_s of nat_shape

(* Two closed Nat terms of different values: the types cannot be converted, the argument is left as is. *)
exception Other_values

let is_keep = function Keep -> true | _ -> false

(* The shape of the differences of [a] (the argument's type) and [d] (the expected type), and the pairs
   [(x, y)] of the holes: [x] in [a], [y] in [d], of equal value from [transport_min] on, [y] not the same
   literal as [x]. [depth] is the nesting of the place the types come from. *)
let nat_diff st depth a d =
  let pairs = ref [] and count = ref 0 in
  let hole x y =
    match List.find_opt (fun (_, x', y') -> Constr.equal x x' && Constr.equal y y') !pairs with
    | Some (k, _, _) -> Hole k
    | None ->
      let k = !count in
      incr count;
      pairs := (k, x, y) :: !pairs;
      Hole k
  in
  let nat_pair depth a d =
    match (value st depth a, value st depth d) with
    | None, _ | _, None -> None
    | Some va, Some vd ->
      if not (Z.equal va vd) then raise Other_values
      else if Z.lt va transport_min || Constr.equal a d then Some Keep
      else
        match (literal_of st depth a, literal_of st depth d) with
        | Some la, Some ld when Constr.equal la ld -> Some Keep
        | _ -> Some (hole a d)
  in
  let rec go depth a d =
    tick st 1;
    check_depth depth;
    if a == d then Keep
    else
      match nat_pair depth a d with
      | Some s -> s
      | None ->
        let go = go (depth + 1) in
        (match (Constr.kind a, Constr.kind d) with
        | Constr.App _, Constr.App _ ->
          let ha, aa = Constr.decompose_app a and hd, ad = Constr.decompose_app d in
          if Array.length aa <> Array.length ad then Keep
          else
            let sh = go ha hd in
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
  let holes = Array.make !count (a, d) in
  List.iter (fun (k, x, y) -> holes.(k) <- (x, y)) !pairs;
  (shape, holes)

(* [d] with each hole [k] at binder depth [depth] replaced by [hole k depth]. *)
let rec nat_fill shape d depth hole =
  match (shape, Constr.kind d) with
  | Keep, _ -> d
  | Hole k, _ -> hole k depth
  | App_s (sh, sargs), _ ->
    let h, args = Constr.decompose_app d in
    Constr.mkApp (nat_fill sh h depth hole, Array.map2 (fun s c -> nat_fill s c depth hole) sargs args)
  | Prod_s (s1, s2), Constr.Prod (na, t, b) ->
    Constr.mkProd (na, nat_fill s1 t depth hole, nat_fill s2 b (depth + 1) hole)
  | Lambda_s (s1, s2), Constr.Lambda (na, t, b) ->
    Constr.mkLambda (na, nat_fill s1 t depth hole, nat_fill s2 b (depth + 1) hole)
  | LetIn_s (s1, s2, s3), Constr.LetIn (na, v, t, b) ->
    Constr.mkLetIn (na, nat_fill s1 v depth hole, nat_fill s2 t depth hole, nat_fill s3 b (depth + 1) hole)
  | Proj_s s1, Constr.Proj (p, r, c) -> Constr.mkProj (p, r, nat_fill s1 c depth hole)
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

let on_econstr f c = EConstr.Unsafe.to_constr (f (EConstr.of_constr c))

let beta st env depth c =
  if has_beta_redex st depth c then on_econstr (Reductionops.nf_beta env st.sigma) c else c

let retype st env c =
  match on_econstr (Retyping.get_type_of ~lax:true env st.sigma) c with
  | ty -> Some ty
  | exception Retyping.RetypeError _ -> None
let whd_all st env c = on_econstr (Reductionops.whd_all env st.sigma) c

let is_irrelevant_binder na =
  match Context.binder_relevance na with Sorts.Irrelevant -> true | Sorts.Relevant | Sorts.RelevanceVar _ -> false

(* [arg], whose expected type is the SProp type [dom], at the nesting [depth], cast along the lemmas of its
   holes, or [None] when its type differs from [dom] at no pair of closed Nat terms that needs one. *)
let transport_arg st env depth arg dom =
  let dom = beta st env depth dom in
  if not (has_big_nat st depth dom) then None
  else
    match Option.map (fun ty -> nat_diff st depth (beta st env depth ty) dom) (retype st env arg) with
    | exception Other_values -> None
    | None | Some (_, [||]) -> None
    | Some (shape, pairs) ->
      let lemmas = Array.map (fun (x, y) -> nat_eq_lemma st depth x y) pairs in
      if Array.exists Option.is_empty lemmas then None
      else begin
        let nt = st.refs in
        let dl = Vars.lift 1 dom in
        let side k j = if j < k then snd pairs.(j) else fst pairs.(j) in
        let cast p k (x, y) =
          let body = nat_fill shape dl 0 (fun j depth -> if j = k then Constr.mkRel (depth + 1) else side k j) in
          let motive = Constr.mkLambda (Context.anonR, nat_type nt, body) in
          let lemma = Constr.mkConstU (Option.get lemmas.(k), UVars.Instance.empty) in
          app nt.nt_transport [| motive; x; y; lemma; p |]
        in
        let p = ref arg in
        Array.iteri (fun k xy -> p := cast !p k xy) pairs;
        st.count <- st.count + 1;
        Array.iter
          (fun c ->
            let id = Constant.label (Option.get c) in
            if not (List.exists (Id.equal id) st.lemmas) then st.lemmas <- id :: st.lemmas)
          lemmas;
        Some !p
      end

(* [args], the arguments of [f] at the nesting [depth], each SProp argument transported where it needs it. *)
let transport_args st env depth f args =
  let n = Array.length args in
  let out = ref args in
  let set k a =
    if !out == args then out := Array.copy args;
    !out.(k) <- a
  in
  (* [ty] is the type of [f] applied to the arguments before [k], under their binders: [subst] holds those
     arguments, the last first. *)
  let rec loop k ty subst =
    if k < n then
      match Constr.kind ty with
      | Constr.Prod (na, dom, codom) ->
        if is_irrelevant_binder na then
          Option.iter (set k) (transport_arg st env depth !out.(k) (Vars.substl subst dom));
        loop (k + 1) codom (!out.(k) :: subst)
      | _ ->
        let ty = whd_all st env (Vars.substl subst ty) in
        if Constr.isProd ty then loop k ty []
  in
  Option.iter (fun ty -> loop 0 ty []) (retype st env f);
  !out

let rec transport_walk st env depth c =
  tick st 1;
  check_depth depth;
  let walk env = transport_walk st env (depth + 1) in
  let push d = Environ.push_rel d env in
  match Constr.kind c with
  | Constr.App (f, args) ->
    let f' = walk env f in
    let args' = transport_args st env depth f' (CArray.Smart.map (walk env) args) in
    if f' == f && args' == args then c else Constr.mkApp (f', args')
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
   nesting [depth]. *)
let rec transport_result st env depth body ty =
  check_depth depth;
  match (Constr.kind body, Constr.kind ty) with
  | Constr.Lambda (na, t, b), Constr.Prod (_, _, tb) ->
    let env = Environ.push_rel (Context.Rel.Declaration.LocalAssum (na, t)) env in
    let b' = transport_result st env (depth + 1) b tb in
    if b' == b then body else Constr.mkLambda (na, t, b')
  | _ ->
    let irrelevant =
      has_big_nat st depth ty &&
      Sorts.relevance_equal Sorts.Irrelevant
        (EConstr.Unsafe.to_relevance (Retyping.relevance_of_type env st.sigma (EConstr.of_constr ty)))
    in
    if irrelevant then Option.default body (transport_arg st env depth body ty) else body

(* Whether the entry may need the pass: [ty], [body] or the type of a global they name holds one of the
   triggers (the rows' constants, [Nat_double], which every literal from 5000 on holds) or a constant of
   type Nat of value [transport_min] or more. *)
let may_apply st env ty body =
  let big_const depth c = match value st depth c with Some v -> Z.geq v transport_min | None -> false in
  let seen = ref GlobRef.Set_env.empty in
  let rec scan types depth c =
    tick st 1;
    check_depth depth;
    match Constr.kind c with
    | Constr.Const (k, _) ->
      if mem_const k st.triggers || big_const depth c then raise_notrace Found;
      if types then global depth (GlobRef.ConstRef k)
    | Constr.Ind (ind, _) -> if types then global depth (GlobRef.IndRef ind)
    | Constr.Construct (cs, _) -> if types then global depth (GlobRef.ConstructRef cs)
    | _ -> Constr.iter (scan types (depth + 1)) c
  and global depth g =
    if not (GlobRef.Set_env.mem g !seen) then begin
      seen := GlobRef.Set_env.add g !seen;
      scan false (depth + 1) (fst (Typeops.type_of_global_in_context env g))
    end
  in
  try
    scan true 0 ty;
    scan true 0 body;
    false
  with Found -> true

let rec resolve ctx = function
  | Nat_type -> Nat_type
  | Any -> Any
  | Inst (path, ps) -> Inst (ctx.consts path, List.map (resolve ctx) ps)

let make_state ctx env refs entry =
  let rows =
    List.map
      (fun spec ->
        { spec; funs = ctx.consts spec.fun_name; classes = ctx.consts spec.class_name; inst_pat = resolve ctx spec.inst })
      op_specs
  in
  (* The export's function of [op] without universes, as a term, and its [toN] lemma. *)
  let lemmas = Hashtbl.create 3 in
  let rec lemma_of op =
    match Hashtbl.find_opt lemmas op with
    | Some l -> l
    | None ->
      let row = List.find (fun row -> row.spec.op = op) rows in
      let g =
        List.find_map
          (fun c ->
            if UVars.AbstractContext.is_empty (Declareops.constant_polymorphic_context (Environ.lookup_constant c env))
            then Some (Constr.mkConstU (c, UVars.Instance.empty))
            else None)
          row.funs
      in
      let l =
        Option.bind g (fun g ->
            let prev = Option.bind row.spec.prev lemma_of in
            Option.map (fun args -> (g, app (lib_term row.spec.to_n_lemma) args)) (row.spec.lemma_args refs ~prev g))
      in
      Hashtbl.add lemmas op l;
      l
  in
  {
    ctx;
    refs;
    genv = env;
    sigma = Evd.from_env env;
    rows;
    of_nat = ctx.consts [ "OfNat"; "ofNat" ];
    inst_of_nat = ctx.consts [ "instOfNatNat" ];
    triggers = refs.nt_double :: List.concat_map (fun row -> row.funs @ row.classes) rows;
    lemma_of;
    entry;
    steps = budget;
    values = PH.create 97;
    const_values = Cmap_env.empty;
    certs = PH.create 17;
    const_certs = Cmap_env.empty;
    next = 0;
    count = 0;
    lemmas = [];
  }

(* The registrations of the rows' [N] functions and [toN] lemmas. *)
let rows_registered () =
  List.for_all (fun spec -> Rocqlib.has_ref spec.n_fun && Rocqlib.has_ref spec.to_n_lemma) op_specs

let transport ctx env ~entry ty body =
  match refs () with
  | Some refs when rows_registered () -> (
    let st = make_state ctx env refs entry in
    match
      if not (may_apply st env ty body) then None
      else
        let body' = transport_result st env 0 (transport_walk st env 0 body) ty in
        if st.count = 0 then None else Some { value = body'; count = st.count; lemmas = List.rev st.lemmas }
    with
    | r -> r
    | exception Out_of_budget ->
      ctx.log
        Pp.(
          str "the transport pass stops: it needs more than " ++ int budget ++ str " steps or a nesting deeper than "
          ++ int max_depth ++ str "; the value is left as Lean's");
      None
    | exception e when CErrors.noncritical e ->
      ctx.log Pp.(str "the transport pass fails; the value is left as Lean's: " ++ CErrors.print e);
      None)
  | Some _ | None -> None
