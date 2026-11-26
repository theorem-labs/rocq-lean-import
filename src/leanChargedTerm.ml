(* The charged term layer of the transport pass (see the .mli): a budget of steps, the term operations the pass
   runs, each charged to it before the work it pays for, and the memos those operations keep. *)

open Names

exception Out_of_budget

exception Out_of_total

let max_depth = 10_000

let check_depth depth = if depth > max_depth then raise Out_of_budget

(* Size estimates of terms not yet paid for: [None] is a size larger than [max_int] (an estimate that cannot
   be represented, which is never [max_int] itself). Both operands are nonnegative. *)
let add_size a b = match (a, b) with Some a, Some b when a <= max_int - b -> Some (a + b) | _ -> None

(* A hash that reads no module path and no universe, so that the same export costs the same steps in whatever
   file imports it. Before it, a memo slot was [Hashtbl.hash_param 10 100 term], which reads the hash of each
   constant's kernel name (its module path is the importing file's library, Test.<file> for a test) and the
   names and numbers of universe levels (the importer's fresh levels carry the library and a process counter):
   the slots, so the memos' collisions and so the step counts, depended on the file's name. The tests of
   tests/fin_transport_bitwise.v and of revision 8 passed every budget pin compiled as diag_<test>.v (run
   fpport-e1nopatch-20261126t153619) and failed nine of them compiled under their own names (runs
   fpport-plain-20261126t151258 and fpport-e2plain-20261126t153625, the same failures twice, and run
   fpport-same-20261126t154718, the same tests with counters under their own names). The tables' hashes
   below read the label alone for the same reason. *)
let hash_mix h x = ((h * 65599) + x) land max_int

(* By the label of the kernel name, which is the Lean name, never its module path. A key equal by [UserOrd]
   (or [CanOrd]) has the same user (or canonical) name, so the same label. *)
let label_hash kn = Id.hash (KerName.label kn)
let user_constant_hash c = label_hash (Constant.user c)
let canonical_constant_hash c = label_hash (Constant.canonical c)
let user_ind_hash (mi, i) = hash_mix (label_hash (MutInd.user mi)) i

let user_globref_hash = function
  | GlobRef.VarRef id -> hash_mix 1 (Id.hash id)
  | GlobRef.ConstRef c -> hash_mix 2 (user_constant_hash c)
  | GlobRef.IndRef ind -> hash_mix 3 (user_ind_hash ind)
  | GlobRef.ConstructRef (ind, j) -> hash_mix (hash_mix 4 (user_ind_hash ind)) j

(* The hash of a term: its nodes in breadth-first order, at most [hash_visited] of them, until
   [hash_meaningful] of them that carry a value are read (the bounds of [Hashtbl.hash] in the OCaml of the
   Rocq 9.2 cut, whose stdlib (4.14) reads [let hash x = seeded_hash_param 10 100 0 x]). Each node costs a
   constant amount of work but for a name, hashed whole as [Hashtbl.hash] hashes a string. A node carries a
   value when it is a [Rel] (its index), a [Var] (its name), a [Const] (its label), an [Ind] (its label and
   index), a [Construct] (those and the constructor's index), a [Sort] (its kind: [SProp], [Prop], [Set],
   [Type] or a sort of a quality variable, never its universe), a primitive integer, float or string (its
   value), a [Meta] or an [Evar] (its number); a universe instance counts only by whether it is empty. Any
   other node counts by its kind ([Proj] with its field's index, [Fix] and [CoFix] with the index of the body
   they name), and its children are queued: a [Cast]'s term and type, a binder's type and body, a [LetIn]'s
   definition, type and body, an [App]'s head and arguments, a [Case]'s subject, parameters, return type,
   indices and branches, a fixpoint's types and bodies, a [Proj]'s subject, an [Array]'s elements, default
   and type. The queue is a buffer of the module (the hash calls nothing that hashes), emptied after each
   hash so that it keeps no term alive. *)
let hash_meaningful = 10
let hash_visited = 100
let hash_queue = Array.make hash_visited Constr.mkProp

let hash_push tail c =
  if tail < hash_visited then begin
    hash_queue.(tail) <- c;
    tail + 1
  end
  else tail

let rec hash_push_array a i tail =
  if i = Array.length a || tail = hash_visited then tail else hash_push_array a (i + 1) (hash_push tail a.(i))

let rec hash_push_branches brs i tail =
  if i = Array.length brs || tail = hash_visited then tail
  else hash_push_branches brs (i + 1) (hash_push tail (snd brs.(i)))

(* A universe instance by its shape: empty or not; its levels are never read. *)
let instance_hash h u = hash_mix h (if UVars.Instance.is_empty u then 0 else 1)

let sort_hash (s : Sorts.t) =
  match s with Sorts.SProp -> 0 | Sorts.Prop -> 1 | Sorts.Set -> 2 | Sorts.Type _ -> 3 | Sorts.QSort _ -> 4

let rec hash_from h head tail meaningful =
  if head = tail || meaningful = hash_meaningful then begin
    Array.fill hash_queue 0 tail Constr.mkProp;
    h
  end
  else
    let next = head + 1 and value = meaningful + 1 in
    match Constr.kind hash_queue.(head) with
    | Constr.Rel n -> hash_from (hash_mix (hash_mix h 1) n) next tail value
    | Constr.Var id -> hash_from (hash_mix (hash_mix h 2) (Id.hash id)) next tail value
    | Constr.Meta n -> hash_from (hash_mix (hash_mix h 3) n) next tail value
    | Constr.Evar (ev, _) -> hash_from (hash_mix (hash_mix h 4) (Evar.repr ev)) next tail value
    | Constr.Sort s -> hash_from (hash_mix (hash_mix h 5) (sort_hash s)) next tail value
    | Constr.Cast (c, _, t) -> hash_from (hash_mix h 6) next (hash_push (hash_push tail c) t) meaningful
    | Constr.Prod (_, t, b) -> hash_from (hash_mix h 7) next (hash_push (hash_push tail t) b) meaningful
    | Constr.Lambda (_, t, b) -> hash_from (hash_mix h 8) next (hash_push (hash_push tail t) b) meaningful
    | Constr.LetIn (_, b, t, c) ->
      hash_from (hash_mix h 9) next (hash_push (hash_push (hash_push tail b) t) c) meaningful
    | Constr.App (f, args) ->
      hash_from (hash_mix h 10) next (hash_push_array args 0 (hash_push tail f)) meaningful
    | Constr.Const (k, u) ->
      hash_from (instance_hash (hash_mix (hash_mix h 11) (user_constant_hash k)) u) next tail value
    | Constr.Ind (ind, u) ->
      hash_from (instance_hash (hash_mix (hash_mix h 12) (user_ind_hash ind)) u) next tail value
    | Constr.Construct ((ind, j), u) ->
      hash_from (instance_hash (hash_mix (hash_mix (hash_mix h 13) (user_ind_hash ind)) j) u) next tail value
    | Constr.Case (_, _, pms, ((_, p), _), iv, c, brs) ->
      let tail = hash_push (hash_push_array pms 0 (hash_push tail c)) p in
      let tail =
        match iv with Constr.NoInvert -> tail | Constr.CaseInvert { indices } -> hash_push_array indices 0 tail
      in
      hash_from (hash_mix h 14) next (hash_push_branches brs 0 tail) meaningful
    | Constr.Fix ((_, i), (_, tys, bds)) ->
      hash_from (hash_mix (hash_mix h 15) i) next (hash_push_array bds 0 (hash_push_array tys 0 tail)) meaningful
    | Constr.CoFix (i, (_, tys, bds)) ->
      hash_from (hash_mix (hash_mix h 16) i) next (hash_push_array bds 0 (hash_push_array tys 0 tail)) meaningful
    | Constr.Proj (p, _, c) ->
      hash_from (hash_mix (hash_mix h 17) (Projection.arg p)) next (hash_push tail c) meaningful
    | Constr.Int i -> hash_from (hash_mix (hash_mix h 18) (Uint63.hash i)) next tail value
    | Constr.Float f -> hash_from (hash_mix (hash_mix h 19) (Float64.hash f)) next tail value
    | Constr.String s -> hash_from (hash_mix (hash_mix h 20) (Pstring.hash s)) next tail value
    | Constr.Array (u, elems, def, ty) ->
      hash_from (instance_hash (hash_mix h 21) u) next
        (hash_push (hash_push (hash_push_array elems 0 tail) def) ty)
        meaningful

let term_hash c =
  hash_queue.(0) <- c;
  hash_from 0 0 1 0

(* The memo of one kind of result, keyed by a term itself: [memo_slots] slots, each empty or holding one term
   with its result, the array allocated by the first write. A term goes to the slot [term_hash term] (above)
   [land (memo_slots - 1)], after the hash's higher bits are folded into its lower ones: a read compares the
   term in that slot with [==] only, a write replaces what the slot holds. There is no probing, resizing or
   structural comparison, so a read or a write costs at most one comparison, whatever the terms that share a
   slot (a unary literal puts every suffix of its successor chain in the same slot); a term whose result was
   replaced is computed again, at its full charge. *)
let memo_slots = 512

type 'a memo = { mutable slots : (Constr.t * 'a) option array }

let memo () = { slots = [||] }

let memo_slot c =
  let h = term_hash c in
  (h lxor (h lsr 9) lxor (h lsr 18)) land (memo_slots - 1)

(* A table of keys with their hash (one of the label hashes above, which read no module path): an array of
   buckets, each a list of keys with their values. It never evicts: a key added stays until the entry ends. *)
type ('k, 'a) table = {
  hash : 'k -> int;
  eq : 'k -> 'k -> bool;
  mutable buckets : ('k * 'a) list array;
  mutable entries : int;
}

let table hash eq = { hash; eq; buckets = Array.make 16 []; entries = 0 }

type t = {
  genv : Environ.env;
  mutable steps : int;
  mutable total : int;
  sizes : int option memo;
  free : int memo;
  normal : Constr.t memo;
}

let create genv ~steps ~total = { genv; steps; total; sizes = memo (); free = memo (); normal = memo () }

(* Both budgets are at most [max_int] and nonnegative before, so neither subtraction can overflow. *)
let tick ch n =
  ch.steps <- ch.steps - n;
  ch.total <- ch.total - n;
  if ch.steps < 0 then raise Out_of_budget;
  if ch.total < 0 then raise Out_of_total

let pay ch = function None -> raise Out_of_budget | Some n -> tick ch n

let memo_get ch m c =
  tick ch 1;
  if Array.length m.slots = 0 then None
  else match m.slots.(memo_slot c) with Some (k, v) when k == c -> Some v | Some _ | None -> None

let memo_put ch m c v =
  tick ch 1;
  if Array.length m.slots = 0 then m.slots <- Array.make memo_slots None;
  m.slots.(memo_slot c) <- Some (c, v)

(* A lookup pays one step and one more for each entry of its bucket it compares; an addition pays one step,
   and, when the table holds twice as many entries as buckets, the copy of every entry into twice as many
   buckets first. *)
let table_find ch t k =
  tick ch 1;
  let rec look = function
    | [] -> None
    | (k', v) :: rest ->
      tick ch 1;
      if t.eq k k' then Some v else look rest
  in
  look t.buckets.(t.hash k land (Array.length t.buckets - 1))

let table_add ch t k v =
  let n = Array.length t.buckets in
  if t.entries >= 2 * n then begin
    tick ch (t.entries + (2 * n));
    let wide = Array.make (2 * n) [] in
    Array.iter
      (List.iter (fun ((k, _) as e) ->
           let i = t.hash k land ((2 * n) - 1) in
           wide.(i) <- e :: wide.(i)))
      t.buckets;
    t.buckets <- wide
  end;
  tick ch 1;
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

(* A leaf without a de Bruijn index: a constant, constructor, inductive type, sort, variable or literal. *)
let closed_leaf c =
  match Constr.kind c with
  | Constr.Var _ | Constr.Meta _ | Constr.Sort _ | Constr.Const _ | Constr.Ind _ | Constr.Construct _ | Constr.Int _
  | Constr.Float _ | Constr.String _ ->
    true
  | _ -> false

let is_leaf c = Constr.isRel c || closed_leaf c

(* The universe data a node holds itself, which [Vars.subst_instance_constr] substitutes (theorem-labs/rocq at
   07e45e36, kernel/vars.ml): the instance of a constant, inductive type, constructor, match or array, and the
   levels (and quality) of a sort. *)
let universe_data c =
  let inst u =
    let q, l = UVars.Instance.length u in
    q + l
  in
  match Constr.kind c with
  | Constr.Const (_, u) | Constr.Ind (_, u) | Constr.Construct (_, u) | Constr.Case (_, u, _, _, _, _, _)
  | Constr.Array (u, _, _, _) ->
    inst u
  | Constr.Sort (Sorts.Type l) -> List.length (Univ.Universe.repr l)
  | Constr.Sort (Sorts.QSort (_, l)) -> 1 + List.length (Univ.Universe.repr l)
  | _ -> 0

(* The term under a run of applications of closed leaves to one argument each ([Nat_succ (Nat_succ ...)], a
   unary literal of the importer), the length [j] of the run and [u] plus the universe data of its heads: one
   step for each application, which the loop reads and follows, so that a reader of the memos below looks up
   only the run's top. *)
let rec unary_run ch c j u =
  match Constr.kind c with
  | Constr.App (h, [| x |]) when closed_leaf h ->
    tick ch 1;
    unary_run ch x (j + 1) (u + universe_data h)
  | _ -> (c, j, u)

(* The number of nodes of [c] as a tree, its shared subterms counted at each occurrence, each node with its own
   universe data, computed on the shared term: what a walk of [c] by Rocq ([Vars.lift], [Vars.substl],
   [Vars.subst_instance_constr]) visits. *)
let rec size ch depth c =
  if is_leaf c then Some (1 + universe_data c)
  else begin
    check_depth depth;
    match memo_get ch ch.sizes c with
    | Some s -> s
    | None ->
      let s =
        match unary_run ch c 0 0 with
        | b, j, u when j > 0 ->
          (* each application of the run and its head: [2 * j] nodes, fewer than the nodes in memory *)
          add_size (Some ((2 * j) + u)) (size ch (depth + 1) b)
        | _ ->
          tick ch (node_steps c);
          Constr.fold
            (fun acc c -> match acc with None -> None | Some _ -> add_size acc (size ch (depth + 1) c))
            (Some (1 + universe_data c))
            c
      in
      memo_put ch ch.sizes c s;
      s
  end

(* The greatest de Bruijn index free in [c] (0 when [c] is closed), of [c] itself: a visit under [k] binders
   reads it against [k]. *)
let rec free ch depth c =
  match Constr.kind c with
  | Constr.Rel i -> i
  | _ when closed_leaf c -> 0
  | _ -> (
    check_depth depth;
    match memo_get ch ch.free c with
    | Some f -> f
    | None ->
      let f =
        match unary_run ch c 0 0 with
        | b, j, _ when j > 0 -> free ch (depth + 1) b
        | _ ->
          tick ch (node_steps c);
          Constr.fold_constr_with_binders succ (fun k acc c -> max acc (free ch (depth + 1) c - k)) 0 0 c
      in
      memo_put ch ch.free c f;
      f)

let closed ch depth c = free ch depth c = 0

(* [Constr.equal], each pair of nodes it compares charged as a visit of the first: [Constr.compare_head_gen]
   reads the node and its immediate subterms (an application's whole argument array); physically equal terms
   are equal at once. *)
let rec equal ch depth a b =
  a == b
  ||
  (tick ch (node_steps a);
   check_depth depth;
   Constr.compare_head_gen
     (fun _ u u' -> UVars.Instance.equal u u')
     Sorts.equal
     (fun (e, l) (e', l') -> Evar.equal e e' && SList.equal (equal ch (depth + 1)) l l')
     (fun _ a b -> equal ch (depth + 1) a b)
     0 a b)

(* [Vars.lift n c], paid before: Rocq's lift walks and may copy the whole tree of [c] (theorem-labs/rocq at
   07e45e36, kernel/constr.ml [exliftn]: [map_with_binders]), which a closed [c] does not need. *)
let lift_ch ch depth n c =
  if n = 0 || closed ch depth c then c
  else begin
    pay ch (size ch depth c);
    Vars.lift n c
  end

(* [c] under [k] binders that take [args.(lo)] to [args.(lo + k - 1)] (the last for [Rel 1]), with them
   substituted ([Vars.substl] of that slice reversed), each node charged before it is read or copied, and the
   [k] marks of the replacements already placed paid first. It goes only into the subterms with a free index
   its substitution changes. A replacement substituted at more than one place duplicates itself: each place
   after its first pays the size of the replacement as a tree, the work a later walk of the result will do
   there, so a substitution that would build a term of more than [max_int] nodes stops before it is made; and
   a replacement under binders pays its lift. *)
let subst_walk ch depth args lo k c =
  if k = 0 then c
  else begin
    tick ch k;
    let placed = Array.make k false in
    let rec go depth n c =
      if free ch depth c <= n then c
      else begin
        tick ch (node_steps c);
        check_depth depth;
        match Constr.kind c with
        | Constr.Rel i -> if i - n <= k then place depth n (k - (i - n)) else Constr.mkRel (i - k)
        | _ -> Constr.map_with_binders succ (go (depth + 1)) n c
      end
    and place depth n j =
      let v = args.(lo + j) in
      if placed.(j) then pay ch (size ch depth v) else placed.(j) <- true;
      lift_ch ch depth n v
    in
    go depth 0 c
  end

let subst1_ch ch depth v c = subst_walk ch depth [| v |] 0 1 c

(* [Constr.mkApp (f, args)]: a copy of both argument arrays when [f] is itself an application. *)
let app_ch ch f args =
  if Array.length args = 0 then f
  else begin
    tick ch (Array.length args + (match Constr.kind f with Constr.App (_, a) -> Array.length a | _ -> 0));
    Constr.mkApp (f, args)
  end

(* [Array.sub a i n], charged. *)
let sub_ch ch a i n =
  tick ch n;
  Array.sub a i n

(* [CArray.Smart.map f a], the copy of [a] charged when an element changes. *)
let smart_map_ch ch f a =
  let n = Array.length a in
  let rec go i =
    if i = n then a
    else
      let x' = f a.(i) in
      if x' == a.(i) then go (i + 1)
      else begin
        tick ch n;
        let a' = Array.copy a in
        a'.(i) <- x';
        for j = i + 1 to n - 1 do
          a'.(j) <- f a.(j)
        done;
        a'
      end
  in
  go 0

(* [c] at the universe instance [u]: for a nonempty [u] Rocq's [Vars.subst_instance_constr] walks and copies
   the whole tree of [c] and substitutes into the universe data of each of its nodes (theorem-labs/rocq at
   07e45e36, kernel/vars.ml), so the [size] of [c], which counts that data, and [u] are paid first; at the
   empty instance [c] is used as it is. *)
let instantiate ch depth u c =
  if UVars.Instance.is_empty u then c
  else begin
    let q, l = UVars.Instance.length u in
    pay ch (add_size (size ch depth c) (Some (q + l)));
    Vars.subst_instance_constr u c
  end

let const_decl ch k =
  tick ch 1;
  Environ.lookup_constant_opt k ch.genv

let def_body ch depth u cb =
  match cb.Declarations.const_body with Declarations.Def b -> Some (instantiate ch depth u b) | _ -> None

let max_head_steps = 64

(* [f] applied to [args]: each leading lambda of [f] takes an argument, one step each, and the binder after [k]
   taken ones only when [k < fits]; then one substitution of the [k] arguments taken, and the rest applied:
   the term and [k], or [None] when a binder does not fit (nothing is substituted then). *)
let apply_lambdas ch depth ~fits f args =
  let nargs = Array.length args in
  let rec peel f k =
    if k = nargs then Some (f, k)
    else
      match Constr.kind f with
      | Constr.Lambda (_, _, b) ->
        if k >= fits then None
        else begin
          tick ch 1;
          peel b (k + 1)
        end
      | _ -> Some (f, k)
  in
  match peel f 0 with
  | None -> None
  | Some (body, k) ->
    let c = subst_walk ch depth args 0 k body in
    Some
      ((if k = nargs then c else if k = 0 then app_ch ch c args else app_ch ch c (sub_ch ch args k (nargs - k))), k)

let never _ = false

(* [c] in [env] reduced at its head, [n] steps taken before: by unfolding a constant (not an opaque one),
   beta, zeta, a cast, a local definition of [env], and projecting a constructor's field, until [stop] holds of
   the term (default: never). The result has the number of steps after, which counts the steps that reduce the
   subject of a projection too, and the head and arguments where it stops. [stop] is tested at each step, after
   its step, nesting and count are checked and before it reduces anything; never on the subject of a projection,
   which is reduced to a constructor. A projection's step is taken before its subject is reduced, and the
   subject is one level deeper ([depth]), so that a nest of projections stops at [max_head_steps] steps. [None]
   at a projection of anything but a constructor, or once the term would take more than [max_head_steps]
   steps: the count is checked before each step's substitution. Unlike [Reductionops.whd_all] it reduces no
   match or fixpoint, and every step and every substitution and copy is charged. *)
let rec whd ?(stop = never) ch env depth n c =
  tick ch 1;
  check_depth depth;
  if n > max_head_steps then None
  else
    let h, args = Constr.decompose_app c in
    if stop c then Some (n, h, args)
    else
      match Constr.kind h with
      | Constr.Const (k, u) -> (
        if n + 1 > max_head_steps then None
        else
          let body = match const_decl ch k with Some cb -> def_body ch depth u cb | None -> None in
          match body with
          | Some body -> (
            match apply_lambdas ch depth ~fits:(max_head_steps - (n + 1)) body args with
            | Some (c, j) -> whd ~stop ch env depth (n + 1 + j) c
            | None -> None)
          | None -> Some (n, h, args))
      | Constr.Lambda _ when Array.length args > 0 -> (
        match apply_lambdas ch depth ~fits:(max_head_steps - n) h args with
        | Some (c, j) -> whd ~stop ch env depth (n + j) c
        | None -> None)
      | Constr.LetIn (_, v, _, b) ->
        if n + 1 > max_head_steps then None
        else whd ~stop ch env depth (n + 1) (app_ch ch (subst1_ch ch depth v b) args)
      | Constr.Cast (c, _, _) ->
        if n + 1 > max_head_steps then None else whd ~stop ch env depth (n + 1) (app_ch ch c args)
      | Constr.Proj (p, _, s) -> (
        match whd ch env (depth + 1) (n + 1) s with
        | Some (n, sh, sargs) when Constr.isConstruct sh ->
          let i = Projection.npars p + Projection.arg p in
          if i < Array.length sargs then whd ~stop ch env depth n (app_ch ch sargs.(i) args) else None
        | _ -> None)
      | Constr.Rel k -> (
        match Environ.lookup_rel k env with
        | Context.Rel.Declaration.LocalDef (_, b, _) ->
          if n + 1 > max_head_steps then None
          else whd ~stop ch env depth (n + 1) (app_ch ch (lift_ch ch depth k b) args)
        | Context.Rel.Declaration.LocalAssum _ -> Some (n, h, args)
        | exception Not_found -> None)
      | _ -> Some (n, h, args)

exception Found

let has_beta_redex ch depth c =
  let rec scan depth c =
    tick ch 1;
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
let rec nf_beta ch depth c =
  if is_leaf c then c
  else begin
    check_depth depth;
    match memo_get ch ch.normal c with
    | Some r -> r
    | None ->
      let r =
        match unary_run ch c 0 0 with
        | b, j, _ when j > 0 ->
          let b' = nf_beta ch (depth + 1) b in
          if b' == b then c
          else
            let rec copy c =
              if c == b then b'
              else
                match Constr.kind c with
                | Constr.App (h, [| x |]) ->
                  tick ch (node_steps c);
                  Constr.mkApp (h, [| copy x |])
                | _ -> assert false
            in
            copy c
        | _ -> (
          tick ch (node_steps c);
          match Constr.kind c with
          | Constr.App (f, args) -> (
            let f' = nf_beta ch (depth + 1) f in
            let args' = CArray.Smart.map (nf_beta ch (depth + 1)) args in
            match Constr.kind f' with
            | Constr.Lambda _ -> (
              (* every binder fits: the contraction cannot refuse one *)
              match apply_lambdas ch depth ~fits:max_int f' args' with
              | Some (r, _) -> nf_beta ch (depth + 1) r
              | None -> assert false)
            | _ -> if f' == f && args' == args then c else app_ch ch f' args')
          | _ -> Constr.map (nf_beta ch (depth + 1)) c)
      in
      memo_put ch ch.normal c r;
      if r != c then memo_put ch ch.normal r r;
      r
  end

let beta ch depth c = if has_beta_redex ch depth c then nf_beta ch depth c else c

let const_type ch depth k u =
  match const_decl ch k with
  | Some cb -> Some (instantiate ch depth u cb.Declarations.const_type)
  | None -> None

let ind_type ch depth ind u =
  tick ch 1;
  let mib, mip = Inductive.lookup_mind_specif ch.genv ind in
  match mib.Declarations.mind_template with
  | Some _ -> None
  | None -> Some (instantiate ch depth u mip.Declarations.mind_user_arity)

let ctor_type ch depth (ind, i) u =
  tick ch 1;
  let mib, mip = Inductive.lookup_mind_specif ch.genv ind in
  match mib.Declarations.mind_template with
  | Some _ -> None
  | None -> Some (instantiate ch depth u mip.Declarations.mind_user_lc.(i - 1))

let expose_prod ch env depth ty =
  match whd ch env depth 0 ty with
  | Some (_, h, [||]) when Constr.isProd h -> Some h
  | Some _ | None -> None

let expose_sort ch env depth ty =
  match whd ch env depth 0 ty with
  | Some (_, h, [||]) when Constr.isSort h -> Some (Constr.destSort h)
  | Some _ | None -> None

let rec type_of ch env depth c =
  tick ch 1;
  check_depth depth;
  match Constr.kind c with
  | Constr.Rel k -> (
    match Environ.lookup_rel k env with
    | decl -> Some (lift_ch ch depth k (Context.Rel.Declaration.get_type decl))
    | exception Not_found -> None)
  | Constr.Const (k, u) -> const_type ch depth k u
  | Constr.Ind (ind, u) -> ind_type ch depth ind u
  | Constr.Construct (cstr, u) -> ctor_type ch depth cstr u
  | Constr.App (f, args) -> (
    match type_of ch env (depth + 1) f with Some ty -> apply_type ch env depth ty args | None -> None)
  | Constr.Lambda (na, t, b) -> (
    match type_of ch (Environ.push_rel (Context.Rel.Declaration.LocalAssum (na, t)) env) (depth + 1) b with
    | Some tb -> Some (Constr.mkProd (na, t, tb))
    | None -> None)
  | Constr.LetIn (na, v, t, b) -> (
    match type_of ch (Environ.push_rel (Context.Rel.Declaration.LocalDef (na, v, t)) env) (depth + 1) b with
    | Some tb -> Some (subst1_ch ch depth v tb)
    | None -> None)
  | Constr.Cast (_, _, t) -> Some t
  | Constr.Proj (p, _, s) -> (
    match type_of ch env (depth + 1) s with
    | None -> None
    | Some sty -> (
      match whd ch env (depth + 1) 0 sty with
      | Some (_, h, params) -> (
        match Constr.kind h with
        | Constr.Ind (ind, u) when Ind.CanOrd.equal ind (Projection.inductive p) ->
          (* the projection's type is under the record's parameters and the record: [params] then [s] *)
          let np = Array.length params in
          tick ch (1 + np);
          let subst = Array.make (np + 1) s in
          Array.blit params 0 subst 0 np;
          let _, pty = Environ.lookup_projection p env in
          Some (subst_walk ch depth subst 0 (np + 1) (instantiate ch depth u pty))
        | _ -> None)
      | None -> None))
  | Constr.Var _ | Constr.Meta _ | Constr.Evar _ | Constr.Sort _ | Constr.Prod _ | Constr.Case _ | Constr.Fix _
  | Constr.CoFix _ | Constr.Int _ | Constr.Float _ | Constr.String _ | Constr.Array _ ->
    None

(* [ty], the type of a function, applied to [args]: its products take them, each charged, and the arguments
   are substituted at the end or where a product must be exposed, as the slice of [args] taken since the last
   substitution. *)
and apply_type ch env depth ty args =
  let n = Array.length args in
  (* [ty] is under the products that took [args.(lo)] to [args.(i - 1)] *)
  let rec loop i lo ty =
    if i = n then Some (subst_walk ch depth args lo (i - lo) ty)
    else begin
      tick ch 1;
      match Constr.kind ty with
      | Constr.Prod (_, _, b) -> loop (i + 1) lo b
      | _ -> (
        match expose_prod ch env depth (subst_walk ch depth args lo (i - lo) ty) with
        | Some p -> loop i i p
        | None -> None)
    end
  in
  loop 0 0 ty

let rec type_relevance ch env depth ty =
  tick ch 1;
  check_depth depth;
  match Constr.kind ty with
  | Constr.Prod (na, t, b) ->
    type_relevance ch (Environ.push_rel (Context.Rel.Declaration.LocalAssum (na, t)) env) (depth + 1) b
  | _ -> (
    match type_of ch env depth ty with
    | Some s -> Option.map Sorts.relevance_of_sort (expose_sort ch env depth s)
    | None -> None)

let print_bound = 256

exception Too_large

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
