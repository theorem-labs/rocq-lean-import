(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Univ
open UVars
module RelDecl = Context.Rel.Declaration
open LeanExpr

let __ () = assert false
let invalid = Constr.(mkApp (mkSet, [| mkSet |]))

let add_universe l ~lbound g =
  let g = UGraph.add_universe l ~strict:false g in
  UGraph.enforce_constraint (lbound, Le, l) g

let quickdef ~name ~types ~univs body =
  let entry = Declare.definition_entry ?types ~univs body in
  let scope = Locality.(Global ImportDefaultBehavior) in
  let kind = Decls.(IsDefinition Definition) in
  let uctx =
    UState.empty
    (* used for ubinders and hook *)
  in
  Declare.declare_entry ~name ~scope ~kind ~impargs:[] ~uctx entry

type extended_level = Level of Level.t | LSProp

type scheme_family = SchemeSProp | SchemeType

(** produce [args, recargs] inside mixed context [args/recargs] [info] is in
    reverse order, ie the head is about the last arg in application order

    examples: [] -> [],[] [false] -> [1],[] [true] -> [2],[1] [true;false] ->
    [3;2],[1] [false;true] -> [3;1],[2] [false;false] -> [2;1],[] [true;true] ->
    [4;2],[3;1] *)
let reorder_inside_core info =
  let rec aux i args recargs = function
    | [] -> (args, recargs)
    | false :: info -> aux (i + 1) (i :: args) recargs info
    | true :: info -> aux (i + 2) ((i + 1) :: args) (i :: recargs) info
  in
  aux 1 [] [] info

let reorder_inside info =
  let args, recargs = reorder_inside_core info in
  CArray.map_of_list Constr.mkRel (List.append args recargs)

let rec insert_after k ((n, t) as v) c =
  if k = 0 then Constr.mkProd (n, t, Vars.lift 1 c)
  else
    match Constr.kind c with
    | Prod (na, a, b) -> Constr.mkProd (na, a, insert_after (k - 1) v b)
    | _ -> assert false

let insert_after k (n, t) c =
  insert_after k (n, Vars.lift k t) (Vars.subst1 invalid c)

let rec reorder_outside info hyps c =
  match (info, hyps) with
  | [], [] -> (c, 0)
  | false :: info, (n, t) :: hyps ->
    let c, k = reorder_outside info hyps c in
    (Constr.mkProd (n, t, c), k + 1)
  | true :: info, (n, t) :: rhyp :: hyps ->
    let c, k = reorder_outside info hyps c in
    let c = insert_after k rhyp c in
    (Constr.mkProd (n, t, c), k + 1)
  | _ -> assert false

(** produce [forall args recargs, P (C args)] from mixed
    [forall args/recargs, P (C args)] *)
let reorder_outside info ft =
  let hyps, out = Term.decompose_prod ft in
  fst (reorder_outside (List.rev info) (List.rev hyps) out)

exception Occur

let occur_mind mind term =
  let rec occur_rec c =
    match Constr.kind c with
    | Constr.Ind ((mind', _), _) ->
      if MutInd.UserOrd.equal mind mind' then raise_notrace Occur
    | _ -> Constr.iter occur_rec c
  in
  try
    occur_rec term;
    true
  with Occur -> false

(** Build the body of a Lean-style scheme. [u] instantiates the inductive, [s]
    is [None] for the SProp scheme and [Some l] for a scheme with motive [l].

    Lean schemes differ from Coq schemes:
    - the motive universe is the first bound universe for Lean but the last for
      Coq (handled by caller)
    - Lean puts induction hypotheses after all the constructor arguments, Coq
      puts them immediately after the corresponding recursive argument. *)
let lean_scheme env ~dep mind u s =
  let mib = Global.lookup_mind mind in
  let nparams = mib.mind_nparams in
  assert (Array.length mib.mind_packets = 1);
  (* if we start using non recursive params in the translation it will
     involve reordering arguments *)
  assert (nparams = mib.mind_nparams_rec);
  let mip = mib.mind_packets.(0) in

  let body =
    let sigma = Evd.from_env env in
    let sigma, s' = match s with
      | LSProp -> sigma, EConstr.ESorts.sprop
      | Level _ ->
        let sigma, u = Evd.new_univ_level_variable UnivRigid sigma in
        sigma, EConstr.ESorts.make @@ Sorts.sort_of_univ @@ Universe.make u
    in
    let sigma, body =
      Indrec.build_induction_scheme env sigma
        ((mind, 0), EConstr.EInstance.make u)
        dep s'
    in
    let body = EConstr.Unsafe.to_constr body in
    let uctx = Evd.sort_context_set sigma in
    match s with
    | LSProp ->
      assert (UnivGen.is_empty_sort_context uctx);
      body
    | Level s ->
      let (_, us), cst = uctx in
      assert (
        Level.Set.cardinal us = 1 && PConstraints.is_empty cst);
      let v = Level.Set.choose us in
      Vars.subst_univs_level_constr
        (Sorts.QVar.Map.empty, Level.Map.singleton v s)
        body
  in

  assert (
    CArray.for_all2 Int.equal mip.mind_consnrealargs mip.mind_consnrealdecls);
  let recinfo =
    Array.mapi
      (fun i (args, _) ->
        let nargs = mip.mind_consnrealargs.(i) in
        (* skip params *)
        let args = CList.firstn nargs args in
        CList.map
          (fun arg ->
            let t = RelDecl.get_type arg in
            not (occur_mind mind t))
          args)
      mip.mind_nf_lc
  in
  let hasrec =
    (* NB: if the only recursive arg is the last arg, no need for reordering *)
    Array.exists
      (function [] -> false | _ :: info -> List.exists (fun x -> x) info)
      recinfo
  in

  if not hasrec then body
  else
    (* body := fun params P (fc : forall args/recargs, P (C args)) => ...

       becomes

       fun params P (fc : forall args, forall recargs, P (C args)) =>
       body params P (fun args/recargs, fc args recargs)
    *)
    let open Constr in
    let nlc = Array.length recinfo in
    let paramsP, inside = Term.decompose_lambda_n_assum (nparams + 1) body in
    let fcs, inside = Term.decompose_lambda_n nlc inside in
    let fcs = List.rev fcs in

    let body =
      mkApp
        (body, Array.init (nparams + 1) (fun i -> mkRel (nlc + nparams + 1 - i)))
    in
    let body =
      mkApp
        ( body,
          Array.of_list
            (CList.map_i
               (fun i (_, ft) ->
                 let info = recinfo.(i) in
                 if not (List.exists (fun x -> x) info) then mkRel (nlc - i)
                 else
                   let hyps, _ = Term.decompose_prod ft in
                   let args = reorder_inside info in
                   Term.it_mkLambda_or_LetIn
                     (mkApp (mkRel (nlc - i + List.length hyps), args))
                     (List.map (fun (n, t) -> RelDecl.LocalAssum (n, t)) hyps))
               0 fcs) )
    in

    let fcs =
      CList.map_i
        (fun i (n, ft) ->
          let info = recinfo.(i) in
          let ft = reorder_outside info ft in
          RelDecl.LocalAssum (n, ft))
        0 fcs
    in
    let fcs = List.rev fcs in
    let body =
      let open CClosure in
      let open RedFlags in
      let env = Environ.push_rel_context paramsP env in
      let env = Environ.push_rel_context fcs env in
      norm_val (create_clos_infos betaiota env) (create_tab ()) (inject body)
    in
    Term.it_mkLambda_or_LetIn (Term.it_mkLambda_or_LetIn body fcs) paramsP

let with_unsafe_univs f () =
  let flags = Global.typing_flags () in
  Global.set_typing_flags { flags with check_eliminations = false };
  try
    let v = f () in
    Global.set_typing_flags flags;
    v
  with e ->
    let e = Exninfo.capture e in
    Global.set_typing_flags flags;
    Exninfo.iraise e

module N = LeanName

(* Rocq's [Record.Internal], under a name of its own: a push's leak check reads the dotted path
   [Record.Internal.<name>] as a host name. *)
module RecordInternal = Record.Internal

let sort_of_level = function
  | LSProp -> Sorts.sprop
  | Level u -> Sorts.sort_of_univ (Universe.make u)

let univ_of_sort = function
  | Sorts.SProp -> None
  | Prop -> assert false
  | Set -> Some Universe.type0
  | Type u | QSort (_, u) -> Some u

let sort_max (s1 : Sorts.t) (s2 : Sorts.t) =
  match (s1, s2) with
  | SProp, SProp | Prop, Prop | Set, Set -> s1
  | SProp, ((Prop | Set | Type _) as s) | ((Prop | Set | Type _) as s), SProp ->
    s
  | Prop, ((Set | Type _) as s) | ((Set | Type _) as s), Prop -> s
  | Set, Type u | Type u, Set ->
    Sorts.sort_of_univ (Univ.Universe.sup Univ.Universe.type0 u)
  | Type u, Type v -> Sorts.sort_of_univ (Univ.Universe.sup u v)
  | QSort _, _ | _, QSort _ -> assert false

(** [map] goes from lean names to universes (in practice either SProp or a named
    level): the universe parameters of the entry being translated
    ([start_uconv]). A universe name that is not one of them refuses the entry:
    the export gave the entry a level its [levelParams] do not declare. *)
let rec to_universe map = function
  | U.Prop -> Sorts.sprop
  | UNamed n -> (
    match N.Map.find_opt n map with
    | Some l -> sort_of_level l
    | None ->
      let params =
        if N.Map.is_empty map then Pp.str "none"
        else Pp.prlist_with_sep Pp.pr_comma N.pp (List.map fst (N.Map.bindings map))
      in
      CErrors.user_err
        Pp.(
          str "the universe " ++ N.pp n
          ++ str " is not a universe parameter of this entry (its parameters: " ++ params
          ++ str ")"))
  | Succ u -> Sorts.super (to_universe map u)
  | Max (a, b) -> sort_max (to_universe map a) (to_universe map b)
  | IMax (a, b) ->
    let ub = to_universe map b in
    if Sorts.is_sprop ub then ub else sort_max (to_universe map a) ub

let rec do_n f x n = if n = 0 then x else do_n f (f x) (n - 1)

(** in lean, imax(Prop+1,l)+1 <= max(Prop+1,l+1) because:
    - either l=Prop, so Prop+1 <= Prop+1
    - or Prop+1 <= l so l+1 <= l+1

    to simulate this, each named level becomes > Set and we compute maxes
    accordingly *)

let simplify_universe u =
  match Universe.repr u with
  | (l, n) :: (l', n') :: rest when Level.is_set l ->
    if n <= n' + 1 || List.exists (fun (_, n') -> n <= n' + 1) rest then
      List.fold_left
        (fun u (l, n) ->
          Universe.sup u (do_n Universe.super (Universe.make l) n))
        (do_n Universe.super (Universe.make l') n')
        rest
    else u
  | _ -> u

let simplify_sort = function
  | Sorts.Type u -> Sorts.sort_of_univ (simplify_universe u)
  | s -> s

(* Return the biggest [n] such that [Set+n <= u]. Assumes a simplified
   [u] as above. *)
let max_increment u =
  match Universe.repr u with
  | (l, n) :: rest when Level.is_set l -> n
  | l -> List.fold_left (fun m (_, n) -> max m (n + 1)) 0 l

let to_universe map u =
  let u = to_universe map u in
  simplify_sort u

(** Map from [n] to the global level standing for [Set+n] (not including n=0).
*)
let sets : Level.t Int.Map.t ref =
  Summary.ref ~name:"lean-set-surrogates" Int.Map.empty

type uconv = {
  map : extended_level N.Map.t;  (** Map from lean names to Coq universes *)
  levels : Level.t Universe.Map.t;
      (** Map from algebraic universes to levels (only levels representing an
          algebraic) *)
  graph : UGraph.t;
}

let lean_id = Id.of_string "Lean"

let { Goptions.get = lean_fancy_univs } =
  Goptions.declare_bool_option_and_ref
    ~key:[ "Lean"; "Fancy"; "Universes" ]
    ~value:true ()

let level_of_universe_core u =
  let u =
    List.map
      (fun (l, n) ->
        let open Level in
        if is_set l then "Set+" ^ string_of_int n
        else
          match name l with
          | None -> assert false
          | Some name ->
            let d, s, i = UGlobal.repr name in
            let d = DirPath.repr d in
            (match (d, i) with
            | [ name; l ], 0 when Id.equal l lean_id ->
              Id.to_string name ^ if n = 0 then "" else "+" ^ string_of_int n
            | _ -> to_string l))
      u
  in
  let s = (match u with [ _ ] -> "" | _ -> "max__") ^ String.concat "_" u in
  Level.(
    make (UGlobal.make (DirPath.make [ Id.of_string_soft s; lean_id ]) "" 0))

let level_of_universe u =
  let u = Universe.repr u in
  level_of_universe_core u

let level_of_universe u =
  if lean_fancy_univs () then level_of_universe u else UnivGen.fresh_level ()

let update_graph (l, u) (l', u') graph =
  if UGraph.check_leq graph (Universe.super u) u' then
    UGraph.enforce_constraint (l, Lt, l') graph
  else if UGraph.check_leq graph (Universe.super u') u then
    UGraph.enforce_constraint (l', Lt, l) graph
  else if UGraph.check_leq graph u u' then
    UGraph.enforce_constraint (l, Le, l') graph
  else if UGraph.check_leq graph u' u then
    UGraph.enforce_constraint (l', Le, l) graph
  else graph

let is_sets u =
  match Universe.repr u with
  | [ (u, n) ] -> if Level.is_set u then Some n else None
  | _ -> None

(** Find or add a global level for Set+n *)
let rec level_of_sets uconv n =
  if n = 0 then (uconv, Level.set)
  else
    try (uconv, Int.Map.find n !sets)
    with Not_found ->
      let uconv, p = level_of_sets uconv (n - 1) in
      let l =
        if lean_fancy_univs () then level_of_universe_core [ (Level.set, n) ]
        else UnivGen.fresh_level ()
      in
      Global.push_context_set
        (Level.Set.singleton l, UnivConstraints.singleton (p, Lt, l));
      sets := Int.Map.add n l !sets;
      let graph = add_universe l ~lbound:p uconv.graph in
      ({ uconv with graph }, l)

let to_univ_level u uconv =
  match Universe.level u with
  | Some l -> (uconv, l)
  | None ->
    (match is_sets u with
    | Some n -> level_of_sets uconv n
    | None ->
      (match Universe.Map.find_opt u uconv.levels with
      | Some l -> (uconv, l)
      | None ->
        let uconv, mset = level_of_sets uconv (max_increment u) in
        let l = level_of_universe u in
        let graph = add_universe l ~lbound:mset uconv.graph in
        let graph =
          Universe.Map.fold
            (fun u' l' graph -> update_graph (l, u) (l', u') graph)
            uconv.levels graph
        in
        let graph =
          N.Map.fold
            (fun _ l' graph ->
              match l' with
              | LSProp -> graph
              | Level l' -> update_graph (l, u) (l', Universe.make l') graph)
            uconv.map graph
        in
        let uconv =
          { uconv with levels = Universe.Map.add u l uconv.levels; graph }
        in
        (uconv, l)))

(** Definitional height, used for unfolding heuristics.

    The definitional height is the longest sequence of constant unfoldings until
    we get a term without definitions (recursors don't count). *)

let height_cache = Summary.ref ~name:"lean-heights" N.Map.empty

let rec height = function
  | Const (c, _) ->
    (try N.Map.find c !height_cache + 1
     with Not_found ->
       (* non constant, recursor, or just skipped *)
       0)
  | Bound _ | Sort _ -> 0
  | Lam (_, _, a, b) | Pi (_, _, a, b) | App (a, b) -> max (height a) (height b)
  | Let { name = _; ty; v; rest } -> max (height ty) (max (height v) (height rest))
  | Proj (_, _, c) -> height c
  | Nat _ | String _ -> 0

let height n body =
  match N.Map.find_opt n !height_cache with
  | Some h -> h
  | None ->
    let h = height body in
    height_cache := N.Map.add n h !height_cache;
    h

type instantiation = {
  ref : GlobRef.t;
  algs : Universe.t list;
      (** For each extra universe, produce the algebraic it corresponds to (the
          initial universes are replaced by the appropriate Var) *)
}

(*
Lean classifies inductives in the following way:
- inductive landing in always >Prop (even when instantiated to all Prop) -> never squashed
- inductive which has Prop instantiation:
  + no constructor -> never squashed
  + multi constructor -> always squashed
  + 1 constructor
    * no non param arguments
      -> not squashed, special reduction
      typically [eq]
    * all arguments appear in the output type
      -> not squashed, basic reduction
      no real world examples? eg [Inductive foo : nat -> Prop := bar : forall x, foo x.]
      2019 "type theory of lean" implies that there should be special reduction
      but testing says otherwise
    * some arguments don't appear in the output type, but are Prop or recursive
      -> not squashed, basic reduction
      typically [Acc], [and]
    * some non-Prop non-recursive arguments (for some instantiation) don't appear in the output type
      -> squashed
      typically [exists]

Additionally, the recursor is always dependent (since Lean 4)
(this implem detail isn't in the TTofLean paper)
Special reduction also seems restricted to always-Prop types.

NB: in practice (all stdlib and mathlib) the target universe is available without reduction
(ie syntactic arity) even though the system doesn't require it.
so we can just look at it directly (we don't want to implement a reduction system)
Update: now we have correct Coq envs so we could reduce the Coq term?

Difference with Coq:
- a non-Prop instantiation of possibly Prop types will never be squashed
- non squashed possibly-Prop types at a Prop instantiation are squashed
  (unless empty or uip branch)
- we need uip for the special reduction.
  TTofLean sounds like we need an encoding with primitive records
  but testing indicates otherwise (all args in output type case).
- we will always need unsafe flags for [Acc], and possibly for [and].

Instantiating the type with all-Prop may side-effect instantiate
some other globals with Prop that won't actually be used
(assuming the inductive is not used with all-Prop)
This probably doesn't matter much, also if we start using upfront
instantiations it won't matter at all.

Primitive records:
Lean autodetects all record-capable types as having primitive
projections, and also autogenerates the eliminators.
Squashed Props with 1 ctor have primitive projections up to the first non-Prop field.
*)

type squashy = {
  maybe_prop : bool;  (** used for optim, not fundamental *)
  always_prop : bool;
      (** controls special reduction, but we just let Coq do its thing for that
      *)
  lean_squashes : bool;
      (** Self descriptive. We handle necessity of unsafe flags
          per-instantiation. *)
}

let noprop = { maybe_prop = false; always_prop = false; lean_squashes = false }

let pp_squashy { maybe_prop; always_prop; lean_squashes } =
  let open Pp in
  (if maybe_prop then
     if always_prop then str "is always Prop" else str "may be Prop"
   else str "is never Prop")
  ++ spc ()
  ++
  if lean_squashes then str "and is squashed by Lean"
  else str "and is not squashed by Lean"

let coq_squashes graph (entry : Entries.mutual_inductive_entry) =
  let env = Global.env () in
  let env = Environ.set_universes graph env in
  let ind =
    match entry.mind_entry_inds with [ ind ] -> ind | _ -> assert false
  in
  let params = entry.mind_entry_params in
  let ty = ind.mind_entry_arity in
  let env_params = Environ.push_rel_context params env in
  let _, s = Reduction.dest_arity env_params ty in
  (* TODO merge with uip branch *)
  if not (Sorts.is_sprop s) then false
  else
    match ind.mind_entry_lc with
    | [] -> false
    | _ :: _ :: _ -> true
    | [ c ] -> (match Constr.kind c with Rel _ | App _ -> false | _ -> true)

let with_env_evm rels uconv f x =
  (* In non upfront mode,
     because we interleave defining new constants as we encounter them,
     pushing rels and handling local universes,
     we pass just the rel_context_val and merge it with the global env and the uconv here *)
  let env = Global.env () in
  let env = Environ.set_rel_context_val rels env in
  let env = Environ.set_universes uconv.graph env in
  let evd = Evd.from_env env in
  f env evd x

let to_annot rels n t uconv =
  let r =
    with_env_evm rels uconv
      (fun env evd r ->
        let r = Retyping.relevance_of_type env evd r in
        EConstr.Unsafe.to_relevance r)
      (EConstr.of_constr t)
  in
  Context.make_annot (N.to_name n) r

(* bit n of [int_of_univs univs] is 1 iff [List.nth univs n] is SProp *)
let int_of_univs =
  let rec aux i acc = function
    | [] -> (i, acc)
    | u :: rest ->
      (match univ_of_sort u with
      | None -> aux ((i * 2) + 1) acc rest
      | Some u -> aux (i * 2) (u :: acc) rest)
  in
  fun l -> aux 0 [] (List.rev l)

let univ_of_name u =
  if lean_fancy_univs () then
    let u = DirPath.make [ N.to_id u; lean_id ] in
    Level.(make (UGlobal.make u "" 0))
  else UnivGen.fresh_level ()

let start_uconv univs i =
  let uconv =
    {
      graph = Global.universes ();
      map = N.Map.empty;
      levels = Universe.Map.empty;
    }
  in
  let uconv, set1 = level_of_sets uconv 1 in
  let rec aux uconv i = function
    | [] ->
      assert (i = 0);
      uconv
    | u :: univs ->
      let map, graph =
        if i mod 2 = 0 then
          let v = univ_of_name u in
          ( N.Map.add u (Level v) uconv.map,
            add_universe v ~lbound:set1 uconv.graph )
        else (N.Map.add u LSProp uconv.map, uconv.graph)
      in
      aux { uconv with map; graph } (i / 2) univs
  in
  aux uconv i univs

let rec make_unames univs ounivs =
  match (univs, ounivs) with
  | _, [] ->
    List.map (fun u -> Name (Id.of_string_soft (Level.to_string u))) univs
  | _u :: univs, o :: ounivs -> N.to_name o :: make_unames univs ounivs
  | [], _ :: _ -> assert false

let univ_entry_gen { map; levels; graph } ounivs =
  let ounivs =
    CList.map_filter
      (fun u ->
        let v = N.Map.get u map in
        match v with LSProp -> None | Level v -> Some (u, v))
      ounivs
  in
  let ounivs, univs = List.split ounivs in
  let univs, algs =
    if Universe.Map.is_empty levels then (univs, [])
    else
      let univs = List.rev univs in
      (* add the new levels to univs, add constraints between maxes
         (eg max(a,b) <= max(a,b,c)) *)
      let univs, algs =
        Universe.Map.fold
          (fun alg l (univs, algs) -> (l :: univs, alg :: algs))
          levels (univs, [])
      in
      let univs = List.rev univs in
      (univs, algs)
  in
  let uset =
    List.fold_left (fun kept l -> Level.Set.add l kept) Level.Set.empty univs
  in
  let kept = Level.Set.add Level.set uset in
  let kept = Int.Map.fold (fun _ -> Level.Set.add) !sets kept in
  let csts = UGraph.constraints_for ~kept graph in
  let csts =
    UnivConstraints.filter
      (fun (a, _, b) -> Level.Set.mem a uset || Level.Set.mem b uset)
      csts
  in
  let unames = { quals = [||]; univs = Array.of_list (make_unames univs ounivs)} in
  let univs = Instance.of_array ([||], Array.of_list univs) in
  let uctx = UContext.make unames (univs, PConstraints.of_univs csts) in
  let subst = snd (make_instance_subst univs) in
  let algs = List.rev_map (subst_univs_level_universe subst) algs in
  (uctx, algs)

let univ_entry a b =
  let uctx, algs = univ_entry_gen a b in
  ((UState.Polymorphic_entry uctx, UnivNames.empty_binders), algs)

(* TODO restrict univs (eg [has_add : Sort (u+1) -> Sort(u+1)] can
   drop the [u] and keep only the replacement for [u+1]??

   Preserve algebraics in codomain position? *)

let name_for_core n i =
  if i = 0 then N.to_id n
  else Id.of_string (N.to_coq_string n ^ "_inst" ^ string_of_int i)

(* NB collisions for constructors/recursors are still possible but
   should be rare *)
let name_for n i =
  let base = name_for_core n i in
  if not (Global.exists_objlabel base) then base
  else
    (* prevent resetting the number *)
    let base = if i = 0 then base else Id.of_string (Id.to_string base ^ "_") in
    Namegen.next_global_ident_away (Global.safe_env ()) base Id.Set.empty

(* The predeclared lookups below read the registrations with
   [Rocqlib.lib_ref_opt]: a name that is not registered is not predeclared, and
   no handler can mistake another failure of the lookup (a [Control.Timeout] of
   the Lean Entry Timeout) for a missing registration. *)
let get_predeclared_ind_suffixed indn suffix n i =
  if N.equal n (N.append_list N.anon indn) then
    let ind_name = name_for_core n i in
    let reg = "lean." ^ Id.to_string ind_name ^ suffix in
    match Rocqlib.lib_ref_opt reg with
    | None -> None
    | Some (IndRef (ind, 0)) -> Some (ind_name, ind)
    | Some _ ->
      CErrors.user_err
        Pp.(
          str "Bad registration for "
          ++ str reg
          ++ str " expected an inductive.")
  else None

let get_predeclared_ind indn n i = get_predeclared_ind_suffixed indn "" n i

let ctor_first_field_head (ctors : (N.t * LeanExpr.expr) list) : N.t option =
  let open LeanExpr in
  match ctors with
  | [ (_, ty) ] ->
    let rec head = function
      | App (a, _) -> head a
      | Const (n, _) -> Some n
      | _ -> None
    in
    (match ty with Pi (_, _, field_ty, _) -> head field_ty | _ -> None)
  | _ -> None

(** Like [get_predeclared_ind] but looks for an inductive predeclared as a
    definition (using a ".cumul" suffix on the registration). Returns the
    ConstRef of the predeclared definition. *)
let get_predeclared_ind_as_def indn n i =
  if N.equal n (N.append_list N.anon indn) then
    let ind_name = name_for_core n i in
    let reg = "lean." ^ Id.to_string ind_name ^ ".cumul" in
    match Rocqlib.lib_ref_opt reg with
    | None -> None
    | Some (ConstRef c) -> Some (ind_name, c)
    | Some _ ->
      CErrors.user_err
        Pp.(
          str "Bad registration for "
          ++ str reg
          ++ str " expected a constant.")
  else None

let get_predeclared_def defn n i =
  if N.equal n (N.append_list N.anon defn) then
    let def_name = name_for_core n i in
    let reg = "lean." ^ Id.to_string def_name in
    match Rocqlib.lib_ref_opt reg with
    | None -> None
    | Some (ConstRef c) -> Some (def_name, c)
    | Some _ ->
      CErrors.user_err
        Pp.(
          str "Bad registration for " ++ str reg ++ str " expected a constant.")
  else None

type predeclared_ind_kind = Eq | Nat | Nat_le | Or | And | Fin | UInt32 | BitVec | Char
type predeclared_def_kind = UInt32_size | Nat_isValidChar | Nat_pow
type predeclared_ind_as_def_kind = ULift_cumul

(* The path of the export being imported, with its Lean version on the new
   path. [do_input] sets it from the parser before it declares each entry:
   what [LeanParseNdjson.path] read from the NDJSON metadata; the legacy path
   for the old text format. An instance that [ensure_exists] declares later is
   declared on the path saved with its entry (see [on_path]). *)
let current_path = ref LeanParseNdjson.Legacy

let on_new_path () =
  match !current_path with LeanParseNdjson.New _ -> true | LeanParseNdjson.Legacy -> false

(* [on_path path f] computes [f ()] with [path] as the current path, then puts
   back the path it replaced, whether [f] returns or raises. *)
let on_path path f =
  let outer = !current_path in
  current_path := path;
  match f () with
  | v ->
    current_path := outer;
    v
  | exception e ->
    current_path := outer;
    Exninfo.iraise (Exninfo.capture e)

(* The paths a row of the predeclared tables below applies on: both, or only
   the legacy path (the new path imports that entry from the export, as Lean
   defines it). *)
type predeclared_paths = Both_paths | Legacy_path_only

let on_current_path = function
  | Both_paths -> true
  | Legacy_path_only -> not (on_new_path ())

(* Fin-headed ctor -> pre-4.17 [.legacy] record; otherwise default. *)
let get_predeclared_uint32 ~ctors indh n i =
  let try_suffixed suffix = get_predeclared_ind_suffixed indh suffix n i in
  match ctor_first_field_head ctors with
  | Some head when N.equal head (N.append_list N.anon [ "Fin" ]) ->
    (match try_suffixed ".legacy" with
     | Some _ as r -> r
     | None -> try_suffixed "")
  | _ -> try_suffixed ""

let get_predeclared_char ~uint32_is_legacy indh n i =
  let try_suffixed suffix = get_predeclared_ind_suffixed indh suffix n i in
  if uint32_is_legacy then
    match try_suffixed ".legacy" with
    | Some _ as r -> r
    | None -> try_suffixed ""
  else try_suffixed ""

(* The rows of the predeclared inductive types that apply on the current path
   to the Lean name [n]. Each row is the kind, the Lean name, the paths the row
   applies on and the lookup of the predeclared inductive type for that name
   at instance [i], which reads a registration only when it is called (see
   [get_predeclared_ind_some]). *)
let get_predeclared_ind_any ?(ctors = []) ?(uint32_is_legacy = false) n i =
  let std indh () = get_predeclared_ind indh n i in
  let uint32 indh () = get_predeclared_uint32 ~ctors indh n i in
  let char indh () = get_predeclared_char ~uint32_is_legacy indh n i in
  List.filter_map
    (fun (indk, indh, paths, lookup) ->
      if on_current_path paths && N.equal n (N.append_list N.anon indh) then Some (indk, indh, lookup indh)
      else None)
    [
      (Eq, [ "Eq" ], Both_paths, std);
      (Nat, [ "Nat" ], Both_paths, std);
      (Nat_le, [ "Nat"; "le" ], Both_paths, std);
      (Or, [ "Or" ], Both_paths, std);
      (And, [ "And" ], Both_paths, std);
      (Fin, [ "Fin" ], Both_paths, std);
      (UInt32, [ "UInt32" ], Legacy_path_only, uint32);
      (BitVec, [ "BitVec" ], Legacy_path_only, std);
      (Char, [ "Char" ], Legacy_path_only, char);
    ]

let get_predeclared_ind_some ?(ctors = []) ?(uint32_is_legacy = false) n i =
  match
    List.filter_map
      (fun (indk, indh, lookup) -> lookup () |> Option.map (fun x -> (indk, indh, x)))
      (get_predeclared_ind_any ~ctors ~uint32_is_legacy n i)
  with
  | [] -> None
  | [ x ] -> Some x
  | _ :: _ :: _ ->
    CErrors.user_err
      Pp.(str "Multiple predeclared inductive types for " ++ N.pp n)

let get_predeclared_ind_as_def_any n i =
  List.filter_map
    (fun (k, h) ->
      get_predeclared_ind_as_def h n i |> Option.map (fun x -> (k, h, x)))
    [
      (ULift_cumul, [ "ULift" ]);
    ]

let get_predeclared_ind_as_def_some n i =
  match get_predeclared_ind_as_def_any n i with
  | [] -> None
  | [ x ] -> Some x
  | _ :: _ :: _ ->
    CErrors.user_err
      Pp.(str "Multiple predeclared ind-as-def constants for " ++ N.pp n)

(* Each row: the kind, the Lean name and the paths the row applies on. *)
let get_predeclared_def_any n i =
  List.filter_map
    (fun (defk, defh, paths) ->
      if not (on_current_path paths) then None
      else get_predeclared_def defh n i |> Option.map (fun x -> (defk, defh, x)))
    [
      (UInt32_size, [ "UInt32"; "size" ], Legacy_path_only);
      (Nat_isValidChar, [ "Nat"; "isValidChar" ], Legacy_path_only);
      (Nat_pow, [ "Nat"; "pow" ], Legacy_path_only);
    ]

let get_predeclared_def_some n i =
  match get_predeclared_def_any n i with
  | [] -> None
  | [ x ] -> Some x
  | _ :: _ :: _ ->
    CErrors.user_err Pp.(str "Multiple predeclared constants for " ++ N.pp n)

(* let get_predeclared_eq n i = get_predeclared_ind "eq" n i *)
let mk_char_prim = "Char.mk.reflective_prim"
let mk_char_prim_legacy = "Char.legacy.mk.reflective_prim"

let lookup_char_prim_ref () =
  match Rocqlib.lib_ref_opt ("lean." ^ mk_char_prim) with
  | Some c -> c
  | None -> Rocqlib.lib_ref ("lean." ^ mk_char_prim_legacy)

(*
Register Nat_isValidChar as lean.Nat_isValidChar.
Register reflective_Char_mk_prim as lean.Char.mk.reflective_prim. *)
let nat_double = "Nat_double"

(** For each name, the instantiation with all non-sprop univs should always be
    declared, but the instantiations with SProp may be lazily declared. We
    expect small instance lengths (experimentally at most 4 in the stdlib) so we
    represent instantiations as bit fields, bit n is 1 iff universe n is
    instantiated by SProp. *)
let declared : instantiation Int.Map.t N.Map.t ref =
  Summary.ref ~name:"lean-declared-instances" N.Map.empty

(* An entry of an export and the path (with the Lean version) of that export:
   [add_entry] saves it, and [ensure_exists] declares its instances on that
   path, also when an entry of a later export asks for one. *)
type saved_entry = { entry : entry; path : LeanParseNdjson.path }

let entries : saved_entry N.Map.t ref = Summary.ref ~name:"lean-entries" N.Map.empty

let squash_info : squashy N.Map.t ref =
  Summary.ref ~name:"lean-squash-info" N.Map.empty

let add_declared n i inst =
  declared :=
    N.Map.update n
      (function
        | None -> Some (Int.Map.singleton i inst)
        | Some m -> Some (Int.Map.add i inst m))
      !declared

let to_univ_level' u uconv =
  match to_universe uconv.map u with
  | SProp -> (uconv, LSProp)
  | Type u | QSort (_, u) ->
    let uconv, u = to_univ_level u uconv in
    (uconv, Level u)
  | Set -> (uconv, Level Level.set)
  | Prop -> assert false

let empty_env = Environ.empty_rel_context_val
let default_proj_id = Id.of_string "default_proj_id"

type error_mode = Skip | Stop | Fail

let { Goptions.get = error_mode } =
  let print = function Skip -> "Skip" | Stop -> "Stop" | Fail -> "Fail" in
  let interp = function
    | "Skip" -> Skip
    | "Stop" -> Stop
    | "Fail" -> Fail
    | s ->
      CErrors.user_err Pp.(str "Unknown error mode " ++ qstring s ++ str ".")
  in
  Goptions.declare_interpreted_string_option_and_ref ~stage:Interp
    ~key:[ "Lean"; "Error"; "Mode" ]
    ~value:Fail interp print ()

exception MissingQuot

let { Goptions.get = skip_missing_quot } =
  Goptions.declare_bool_option_and_ref ~stage:Interp
    ~key:[ "Lean"; "Skip"; "Missing"; "Quotient" ]
    ~value:true ()

let error_mode = function
  | MissingQuot when skip_missing_quot () -> Skip
  | _ -> error_mode ()

module ZMap = CMap.Make (Z)

let nat_ints = ref ZMap.empty
let max_known_int = ref (Z.pred Z.zero)

let one_more_int nat =
  let i = Z.succ !max_known_int in
  let c =
    if Z.equal i Z.zero then Constr.mkConstructU ((nat, 1), UVars.Instance.empty)
    else
      let cpred = ZMap.get !max_known_int !nat_ints in
      Constr.(
        mkApp (mkConstructU ((nat, 2), UVars.Instance.empty), [| cpred |]))
  in
  nat_ints := ZMap.add i c !nat_ints;
  max_known_int := i

(* A literal below [LeanNatTransport.max_nat_int] is [Nat_succ] applied [i]
   times to [Nat_zero], each predecessor the literal [i - 1] (kept in
   [nat_ints]); from it on, the form [LeanNatTransport.large_literal] builds
   (shared with the transport pass, whose evaluation writes the literals it
   computes in the same form). *)
let nat_int nat double i =
  assert (Z.leq Z.zero i);
  if Z.leq LeanNatTransport.max_nat_int i then LeanNatTransport.large_literal nat double i
  else begin
    while Z.lt !max_known_int i do
      one_more_int nat
    done;
    ZMap.get i !nat_ints
  end

(* The code points of the string literal [s], in order. Lean's strings are
   well-formed UTF-8 (no overlong form, no surrogate, nothing above U+10FFFF,
   no sequence cut short): a literal that is not is refused, on either path. *)
let code_points s =
  let rec rev_code_points i acc =
    if i >= String.length s then acc
    else
      let d = String.get_utf_8_uchar s i in
      if not (Uchar.utf_decode_is_valid d) then
        CErrors.user_err
          Pp.(str "String literal is not well-formed UTF-8 at byte " ++ int i ++ str ".")
      else
        rev_code_points (i + Uchar.utf_decode_length d)
          (Uchar.to_int (Uchar.utf_decode_uchar d) :: acc)
  in
  List.rev (rev_code_points 0 [])

let mk_char mkChar (c : int) =
  Constr.(mkApp (mkChar, [| mkInt (Uint63.of_int c) |]))

let mk_list list uinst ty l =
  let cNil = Constr.(mkApp (mkConstructU ((list, 1), uinst), [| ty |])) in
  let cCons = Constr.mkConstructU ((list, 2), uinst) in
  let rec mk_list_rec l =
    match l with
    | [] -> cNil
    | hd :: tl -> Constr.mkApp (cCons, [| ty; hd; mk_list_rec tl |])
  in
  mk_list_rec l

let mk_string char string list char_uinst mkChar s =
  let chars = List.map (mk_char mkChar) (code_points s) in
  let ls = mk_list list char_uinst char chars in
  Constr.(mkApp (mkConstructU ((string, 1), UVars.Instance.empty), [| ls |]))

(* On the new path, a string literal is translated as the term Lean's kernel
   unfolds it to ([string_lit_to_constructor], Lean v4.25.0
   src/kernel/inductive.cpp:1200-1211): the string constructor applied to the
   list [List.cons.{0} Char (Char.ofNat c)] ... [List.nil.{0} Char] of the
   literal's code points [c], each a natural number literal ([Char.ofNat] is
   set at line 1233). The constructor is [String.mk] up to Lean 4.25.x (v4.25.0
   line 1226) and [String.ofList] from 4.26.0 on (v4.26.0 line 1226): the
   export's [lean.version], [version], chooses. [to_constr] translates the term
   like any other Lean term, so it uses the export's own constructor, [List],
   [Char] and [Char.ofNat]. *)
let string_lit_expr version s =
  let const path us = Const (N.append_list N.anon path, us) in
  let char = const [ "Char" ] [] in
  (* [U.Prop] is Lean's universe level 0, as in the exports. *)
  let list_ctor k = App (const [ "List"; k ] [ U.Prop ], char) in
  let cons rest c =
    App (App (list_ctor "cons", App (const [ "Char"; "ofNat" ] [], LeanExpr.Nat (string_of_int c))), rest)
  in
  let string_ctor = if version < (4, 26, 0) then [ "String"; "mk" ] else [ "String"; "ofList" ] in
  App (const string_ctor [], List.fold_left cons (list_ctor "nil") (List.rev (code_points s)))

(* The Rocq term of the instantiation [inst] at the Rocq universes [univs] of
   the Lean universes that are not SProp (see [int_of_univs]): its [algs] are
   instantiated with them. *)
let instance_term inst univs uconv =
  let subst l =
    let u =
      match Level.var_index l with
      | None -> Universe.make l
      | Some n -> List.nth univs n
    in
    Some u
  in
  let extra =
    List.map
      (fun alg -> simplify_universe (UnivSubst.subst_univs_universe subst alg))
      inst.algs
  in
  let univs = List.concat [ univs; extra ] in
  let uconv, univs =
    CList.fold_left_map (fun uconv u -> to_univ_level u uconv) uconv univs
  in
  let u = Instance.of_array ([||], Array.of_list univs) in
  (uconv, Constr.mkRef (inst.ref, u))

(* The check of an entry of the export bound to a predeclared constant
   ([check_predeclared_def], [check_predeclared_ind], on either path): the
   entry is translated as the importer translates any entry, at the universes
   [start_uconv] gives its instance, and the predeclared constant is taken at
   the same universes, as [instantiate] takes it. A difference refuses the
   entry, with a message that names the entry, the predeclared constant and
   the difference. *)

(* The universes of an entry with the Lean universes [univs] at instance [i],
   and the Rocq universes a predeclared constant is taken at for it. *)
let predeclared_univs univs i =
  let uconv = start_uconv univs i in
  (uconv, snd (int_of_univs (List.map (fun u -> to_universe uconv.map (U.UNamed u)) univs)))

(* Refuse the entry [name] of the export, bound to the predeclared [ref]. *)
let refuse_predeclared name ref difference =
  CErrors.user_err
    Pp.(
      str "The export's " ++ N.pp name ++ str " does not agree with the predeclared "
      ++ Printer.pr_global ref ++ str ": " ++ difference ++ str ".")

(* The type of the predeclared [inst] at the Rocq universes [rocq_univs], with
   the environment to compare it in. *)
let predeclared_type uconv rocq_univs inst =
  let uconv, c = instance_term inst rocq_univs uconv in
  let env = Environ.set_universes uconv.graph (Global.env ()) in
  let evd = Evd.from_env env in
  (uconv, env, EConstr.to_constr evd (Retyping.get_type_of env evd (EConstr.of_constr c)))

(* Compare [export], [what] of the entry [name] of the export, with the type of
   the predeclared [inst] by conversion, and refuse the entry, bound to the
   predeclared [pred], when they differ. *)
let compare_predeclared_type ~name ~pred uconv rocq_univs what export inst =
  let uconv, env, predeclared = predeclared_type uconv rocq_univs inst in
  match Conversion.conv env predeclared export with
  | Ok () -> uconv
  | Error () ->
    let pr = Printer.pr_constr_env env (Evd.from_env env) in
    refuse_predeclared name pred
      Pp.(
        what ++ spc () ++ pr export ++ spc () ++ str "is not convertible with" ++ spc ()
        ++ pr predeclared ++ str ", the type of " ++ Printer.pr_global inst.ref)

(* Compare the type [export] of the inductive type [name] of the export with
   the type of the predeclared [inst] it is bound to, and refuse the entry when
   they differ. The parameters and indices are compared by conversion, and the
   sort exactly: the export's sort, the importer's translation of the sort Lean
   gives the type, must be the one the predeclared type stands for. src/Lean.v
   declares in [Set] the types Lean declares in [Type], so a type predeclared
   in [Set] accepts only the translation of Lean's [Type] ([Type@{Set+1}], see
   [level_of_sets]); a type predeclared in [SProp], or at the universes of the
   entry (as [ULift], predeclared as a definition), accepts only its own
   sort. *)
let compare_predeclared_arity ~name uconv rocq_univs export inst =
  let refuse difference = refuse_predeclared name inst.ref difference in
  let uconv, env, predeclared = predeclared_type uconv rocq_univs inst in
  let evd = Evd.from_env env in
  let export_binders, export_sort = Reduction.dest_arity env export in
  let binders, sort = Reduction.dest_arity env predeclared in
  let in_prop binders = Term.it_mkProd_or_LetIn Constr.mkProp binders in
  if Result.is_error (Conversion.conv env (in_prop binders) (in_prop export_binders)) then begin
    let pr = Printer.pr_constr_env env evd in
    refuse
      Pp.(
        str "its type" ++ spc () ++ pr export ++ spc ()
        ++ str "does not have the parameters and indices of" ++ spc () ++ pr predeclared
        ++ str ", the type of " ++ Printer.pr_global inst.ref)
  end;
  let pr_sort = Printer.pr_sort ~universes:true evd in
  let uconv, expected, rule =
    match sort with
    | Sorts.Set ->
      let uconv, lean_type = to_univ_level' (U.Succ U.Prop) uconv in
      let expected = sort_of_level lean_type in
      ( uconv,
        expected,
        Pp.(
          str "a type predeclared in Set accepts only " ++ pr_sort expected
          ++ str ", the importer's translation of Lean's Type") )
    | _ ->
      ( uconv,
        sort,
        Pp.(
          Printer.pr_global inst.ref ++ str " is in " ++ pr_sort sort
          ++ str ", and a predeclared type accepts only its own sort") )
  in
  match Conversion.conv env (Constr.mkSort expected) (Constr.mkSort export_sort) with
  | Ok () -> uconv
  | Error () -> refuse Pp.(str "its type is in the sort " ++ pr_sort export_sort ++ str ", but " ++ rule)

(* The translation of an inductive type of the export ([translate_ind]): its
   parameters (innermost first), its arity in their context, the indices and
   sort of that arity, and its constructors with their types in the context
   [tr_ctor_env] of the type itself and its parameters. *)
type translated_ind = {
  tr_params : Constr.rel_context;
  tr_arity : Constr.types;
  tr_indices : Constr.rel_context;
  tr_sort : Sorts.t;
  tr_ctor_env : Environ.rel_context_val;
  tr_ctors : (N.t * Constr.types) list;
}

let lcnt = ref 0

(* The line of the import's output about the entry [name] of the current line: "line N: NAME", followed by
   ": MSG" when [msg] is given. *)
let line_msg ?msg name =
  Feedback.msg_info
    Pp.(
      str "line " ++ int !lcnt ++ str ": " ++ N.pp name
      ++ match msg with None -> mt () | Some msg -> str ": " ++ msg)

(* The constants of every declared instance of the export's entry [path]. *)
let lean_consts path =
  match N.Map.find_opt (N.append_list N.anon path) !declared with
  | None -> []
  | Some m ->
    Int.Map.fold (fun _ { ref; _ } acc -> match ref with GlobRef.ConstRef c -> c :: acc | _ -> acc) m []

(* What the transport pass reads of the importer's state, for the entry [name]: the export's constants, a
   way to declare a lemma and a way to log a line about the entry. *)
let nat_transport_context name =
  {
    LeanNatTransport.consts = lean_consts;
    declare =
      (fun id ty c ->
        quickdef ~name:id ~types:(Some ty)
          ~univs:(UState.Polymorphic_entry UContext.empty, UnivNames.empty_binders)
          c);
    log = (fun msg -> line_msg ~msg name);
  }

let rec to_constr =
  let open Constr in
  let ( >>= ) x f uconv =
    let uconv, x = x uconv in
    f x uconv
  in
  let get_uconv uconv = (uconv, uconv) in
  let ret x uconv = (uconv, x) in
  let to_annot env n t u = (u, to_annot env n t u) in
  let push_rel = Environ.push_rel_context_val in
  fun env -> function
    | Bound i -> ret (mkRel (i + 1))
    | Sort univ ->
      to_univ_level' univ >>= fun u -> ret (mkSort (sort_of_level u))
    | Const (n, univs) -> instantiate n univs
    | App (a, b) ->
      to_constr env a >>= fun a ->
      to_constr env b >>= fun b -> ret (mkApp (a, [| b |]))
    | Let { name; ty; v; rest } ->
      to_constr env ty >>= fun ty ->
      to_annot env name ty >>= fun name ->
      to_constr env v >>= fun v ->
      to_constr (push_rel (LocalDef (name, v, ty)) env) rest >>= fun rest ->
      ret (mkLetIn (name, v, ty, rest))
    | Lam (_bk, n, a, b) ->
      to_constr env a >>= fun a ->
      to_annot env n a >>= fun n ->
      to_constr (push_rel (LocalAssum (n, a)) env) b >>= fun b ->
      ret (mkLambda (n, a, b))
    | Pi (_bk, n, a, b) ->
      to_constr env a >>= fun a ->
      to_annot env n a >>= fun n ->
      to_constr (push_rel (LocalAssum (n, a)) env) b >>= fun b ->
      ret (mkProd (n, a, b))
    | Proj (lean_ind, field, c) ->
      to_constr env c >>= fun c ->
      get_uconv >>= fun uconv ->
      (* we retype to get the ind, because otherwise we need the lean
       univs for instantiation
       This means we ignore the lean_ind in the Proj data. *)
      let c =
        with_env_evm env uconv
          (fun env evd () ->
            let tc = Retyping.get_type_of env evd (EConstr.of_constr c) in
            let tc =
              Reductionops.whd_all env evd tc
            in
            let tc_head, args = EConstr.decompose_app evd tc in
            match EConstr.kind evd tc_head with
            | Constr.Ind _ ->
              (* Standard inductive: use normal projection *)
              let ind, u =
                Constr.destInd (EConstr.Unsafe.to_constr tc_head)
              in
              let mib, mip = Inductive.lookup_mind_specif (Global.env()) ind in
              begin
                match mip.mind_record with
                | PrimRecord infos ->
                  let p, r =
                    Declareops.inductive_make_projection ind mib ~proj_arg:field
                  in
                  (* unfolded?? *)
                  mkProj (Projection.make p false, r, c)
                | FakeRecord when Structures.Structure.mem env ind ->
                  (* Non-primitive record (see [declare_ind]): apply its
                     projection constant to the parameters and [c]. *)
                  begin
                    match
                      List.nth_opt
                        (Structures.Structure.find_projections env ind)
                        field
                    with
                    | Some (Some p) ->
                      let params = Array.map EConstr.Unsafe.to_constr args in
                      mkApp (mkConstU (p, u), Array.append params [| c |])
                    | Some None | None ->
                      CErrors.user_err
                        Pp.(
                          str "no projection " ++ int field ++ str " for "
                          ++ N.pp lean_ind)
                  end
                | NotRecord | FakeRecord ->
                  if
                    mip.mind_relevance
                    == EConstr.Unsafe.to_relevance EConstr.ERelevance.irrelevant
                  then
                    CErrors.user_err
                      Pp.(str "TODO projection for non record Prop inductive")
                  else
                    CErrors.user_err
                      Pp.(str "cannot project non record " ++ N.pp lean_ind)
              end
            | _ ->
              (* Type is not an inductive (e.g., transparent cumulative ULift).
                 Projection is the identity. *)
              c)
          ()
      in
      ret c
    | Nat s ->
      (* [nat_ints] is not synchronized so ensure Nat is instantiated *)
      instantiate (N.append N.anon "Nat") [] >>= fun nat ->
      let nat, _ = Constr.destInd nat in
      get_uconv >>= fun uconv ->
      let double =
        with_env_evm env uconv
          (fun env evd () ->
            let _, p =
              Evd.fresh_global env evd (Rocqlib.lib_ref ("lean." ^ nat_double))
            in
            EConstr.to_constr evd p)
          ()
      in
      ret (nat_int nat double (Z.of_string s))
    | String s -> (
      match !current_path with
      | LeanParseNdjson.New version -> to_constr env (string_lit_expr version s)
      | LeanParseNdjson.Legacy ->
        (* instantiate (N.append N.anon "Char") [] >>= fun char -> *)
        (* let (_, charu) = Constr.destInd char in *)
        instantiate (N.append N.anon "String") [] >>= fun string ->
        let string, _ = Constr.destInd string in
        instantiate (N.append (N.append N.anon "String") "mk") []
        >>= fun string_mk ->
        get_uconv >>= fun uconv ->
        let list, char =
          with_env_evm env uconv
            (fun env evd () ->
              let ty =
                Retyping.get_type_of env evd (EConstr.of_constr string_mk)
              in
              let _, list_char, _ = EConstr.destProd evd ty in
              let list, char =
                match EConstr.destApp evd list_char with
                | list, [| char |] -> (list, char)
                | _ ->
                  CErrors.user_err
                    Pp.(
                      str "Invalid type for string constructor: "
                      ++ Printer.pr_type_env env evd (EConstr.to_constr evd ty)
                      ++ str " ("
                      ++ Printer.pr_type_env env evd
                           (EConstr.to_constr evd list_char)
                      ++ str " should be an application of list to char)")
              in
              (EConstr.to_constr evd list, EConstr.to_constr evd char))
            ()
        in
        (* instantiate (N.append N.anon "List") [] >>= fun list -> *)
        let list, _ = Constr.destInd list in
        get_uconv >>= fun uconv ->
        let mkChar =
          with_env_evm env uconv
            (fun env evd () ->
              let _, mkChar =
                Evd.fresh_global env evd (lookup_char_prim_ref ())
              in
              EConstr.to_constr evd mkChar)
            ()
        in
        ret (mk_string char string list UVars.Instance.empty mkChar s))

and instantiate n univs uconv =
  assert (List.length univs < Sys.int_size);
  (* TODO what happens when is_large_elim and the motive is instantiated with Prop? *)
  let univs = List.map (to_universe uconv.map) univs in
  let i, univs = int_of_univs univs in
  instance_term (ensure_exists n i) univs uconv

and ensure_exists n i =
  try !declared |> N.Map.find n |> Int.Map.find i
  with Not_found ->
    (* TODO can we end up asking for a ctor or eliminator before
       asking for the inductive type? *)
    (* if i = 0 then CErrors.user_err Pp.(N.pp n ++ str " was not instantiated!"); *)
    (* assert (not (upfront_instances ())); *)
    (match N.Map.find n !entries with
    | { entry; path } ->
      on_path path (fun () ->
          match entry with
          | Def def -> declare_def def i
          | Ax ax -> declare_ax ax i
          | Ind ind -> declare_ind ind i
          | Quot _ -> CErrors.user_err Pp.(str "quot must be predeclared"))
    | exception Not_found -> CErrors.user_err Pp.(str "missing " ++ N.pp n))

(* Check the definition [def] of the export against the predeclared constant
   [pred] the importer binds it to at instance [i]: its declared type is
   compared by conversion, not its value (the predeclared value is kept). *)
and check_predeclared_def ({ name; ty; univs; _ } : def) i (pred : instantiation) =
  let uconv, rocq_univs = predeclared_univs univs i in
  let uconv, ty = to_constr empty_env ty uconv in
  ignore
    (compare_predeclared_type ~name ~pred:pred.ref uconv rocq_univs (Pp.str "its declared type") ty
       pred)

(* Check the inductive type [ind] of the export against the predeclared [pred]
   the importer binds it to at instance [i], translated as [declare_ind]
   translates a new inductive type ([translate_ind]): its parameter count
   ([nparams], [None] for a type predeclared as a definition), its type (see
   [compare_predeclared_arity]), its constructor count and each constructor's
   type, by conversion, against the predeclared constructors [pred_ctors] in
   order. *)
and check_predeclared_ind (ind : ind) i ~nparams ~ctors:pred_ctors (pred : instantiation) =
  let count what export predeclared =
    if export <> predeclared then
      refuse_predeclared ind.name pred.ref
        Pp.(
          str "the export gives it " ++ int export ++ str " " ++ str what
          ++ str ", the predeclared one has " ++ int predeclared)
  in
  Option.iter (count "parameters" (List.length ind.params)) nparams;
  let uconv, rocq_univs = predeclared_univs ind.univs i in
  let uconv, t = translate_ind uconv ind in
  let uconv =
    compare_predeclared_arity ~name:ind.name uconv rocq_univs
      (Term.it_mkProd_or_LetIn t.tr_arity t.tr_params)
      pred
  in
  count "constructors" (List.length t.tr_ctors) (List.length pred_ctors);
  let uconv, ind_term = instance_term pred rocq_univs uconv in
  ignore
    (List.fold_left2
       (fun uconv (cname, cty) cinst ->
         let cty = Vars.subst1 ind_term (Term.it_mkProd_or_LetIn cty t.tr_params) in
         compare_predeclared_type ~name:ind.name ~pred:pred.ref uconv rocq_univs
           Pp.(str "the type of its constructor " ++ N.pp cname ++ str ",")
           cty cinst)
       uconv t.tr_ctors pred_ctors)

and declare_def ({ name = n; ty; body; univs; } as def) i =
  let ref, algs =
    match get_predeclared_def_some n i with
    | Some ((UInt32_size | Nat_isValidChar | Nat_pow), _, (def_name, c)) ->
      (* Hack to let the user predeclare some constants
         TODO make a more general Register-like API? *)
      Feedback.msg_info Pp.(Id.print def_name ++ str " is predeclared");
      let ref = GlobRef.ConstRef c in
      check_predeclared_def def i { ref; algs = [] };
      (ref, [])
    | None ->
      let uconv = start_uconv univs i in
      let uconv, ty = to_constr empty_env ty uconv in
      let uconv, body = to_constr empty_env body uconv in
      let id = name_for n i in
      let transported =
        if not (on_new_path ()) then None
        else
          LeanNatTransport.transport (nat_transport_context n)
            (Environ.set_universes uconv.graph (Global.env ()))
            ~entry:id ty body
      in
      let univs, algs = univ_entry uconv univs in
      let declare body =
        try quickdef ~name:id ~types:(Some ty) ~univs body
        with e ->
          let e = Exninfo.capture e in
          (* The term and its type are printed for a failure of the term, not
             for a critical exception such as the [Control.Timeout] of the
             Lean Entry Timeout, which ends the entry at once. *)
          if CErrors.noncritical (fst e) then
            Feedback.msg_info
              Pp.(
                str "Failed with" ++ fnl ()
                ++ Printer.pr_constr_env (Global.env ())
                     (Evd.from_env (Global.env ()))
                     body
                ++ fnl () ++ str ": "
                ++ Printer.pr_constr_env (Global.env ())
                     (Evd.from_env (Global.env ()))
                     ty);
          Exninfo.iraise e
      in
      (* The transported value, when the pass changes it, is declared first. A value the kernel refuses
         is logged at once, and Lean's own value goes to the kernel instead: when that is refused too, the
         entry fails with Lean's error, as without the pass. The kernel's error about the transported value
         is printed only when that value has at most [LeanChargedTerm.print_bound] nodes. *)
      let ref =
        match transported with
        | None -> declare body
        | Some { LeanNatTransport.value; count; lemmas } -> (
          match quickdef ~name:id ~types:(Some ty) ~univs value with
          | ref ->
            line_msg n
              ~msg:
                Pp.(
                  int count ++ str " argument(s) transported ("
                  ++ prlist_with_sep (fun () -> str ", ") Id.print lemmas
                  ++ str ")");
            ref
          | exception e when CErrors.noncritical e ->
            line_msg n
              ~msg:
                (if LeanChargedTerm.printable [ value ] then
                   Pp.(
                     str "the transported value is refused (" ++ CErrors.print e
                     ++ str "); Lean's value goes to the kernel instead")
                 else
                   Pp.(
                     str "the transported value is refused by the kernel (it has more than "
                     ++ int LeanChargedTerm.print_bound
                     ++ str " nodes: the kernel's error is not printed); Lean's value goes to the kernel instead"));
            declare body)
      in
      (ref, algs)
  in
  let () =
    let c = match ref with ConstRef c -> c | _ -> assert false in
    let height = height n body in
    Global.set_strategy (Conv_oracle.EvalConstRef c) (Level (-height))
  in
  let inst = { ref; algs } in
  let () = add_declared n i inst in
  inst

and declare_ax { name = n; ty; univs } i =
  let uconv = start_uconv univs i in
  let uconv, ty = to_constr empty_env ty uconv in
  let univs, algs = univ_entry uconv univs in
  let entry = Declare.(ParameterEntry (parameter_entry ~univs ty)) in
  let c =
    Declare.declare_constant ~name:(name_for n i)
      ~kind:Decls.(IsAssumption Definitional)
      entry
  in
  let inst = { ref = GlobRef.ConstRef c; algs } in
  let () = add_declared n i inst in
  inst

and to_params uconv params =
  let acc, params =
    CList.fold_left_map
      (fun (env, uconv) (_bk, p, ty) ->
        let uconv, ty = to_constr env ty uconv in
        let d = RelDecl.LocalAssum (to_annot env p ty uconv, ty) in
        let env = Environ.push_rel_context_val d env in
        ((env, uconv), d))
      (empty_env, uconv) params
  in
  (acc, List.rev params)

(* The translation of the inductive type [ind] at the universes [uconv], as
   [declare_ind] declares it and [check_predeclared_ind] checks it: the
   parameters, then the arity in their context, then each constructor's type
   in the context of the type itself and its parameters. *)
and translate_ind uconv ({ name; params; ty; ctors; _ } : ind) =
  let (env_params, uconv), params = to_params uconv params in
  let uconv, arity = to_constr env_params ty uconv in
  let indices, sort =
    Reduction.dest_arity
      (Environ.set_rel_context_val env_params
         (Environ.set_universes uconv.graph (Global.env ())))
      arity
  in
  let env_ind =
    Environ.push_rel_context_val
      (LocalAssum
         ( Context.make_annot (N.to_name name) (Sorts.relevance_of_sort sort),
           Term.it_mkProd_or_LetIn arity params ))
      empty_env
  in
  let ctor_env = Context.Rel.fold_outside Environ.push_rel_context_val params ~init:env_ind in
  let uconv, ctors =
    CList.fold_left_map
      (fun uconv (cname, cty) ->
        let uconv, cty = to_constr ctor_env cty uconv in
        (uconv, (cname, cty)))
      uconv ctors
  in
  ( uconv,
    {
      tr_params = params;
      tr_arity = arity;
      tr_indices = indices;
      tr_sort = sort;
      tr_ctor_env = ctor_env;
      tr_ctors = ctors;
    } )

and declare_ind ({ name = n; ctors; univs; _ } as ind) i =
  (* Handle inductives predeclared as definitions (e.g., ULift with cumulativity).
     We check if there's a cumul registration for this specific instance. *)
  match get_predeclared_ind_as_def_some n i with
  | Some (ULift_cumul, _, _) ->
    let def_name = name_for_core n i in
    let cumul_reg nm = "lean." ^ Id.to_string (name_for_core nm i) ^ ".cumul" in
    Feedback.msg_info Pp.(Id.print def_name ++ str " is predeclared (cumulative)");
    (* The Rocq cumul definitions take four universes [r s s1 rs1] where
       [s1] stands for Lean's [s+1] and [rs1] for Lean's [max(r+1, s+1)].
       Lean provides two universes [r; s], so we supply two [algs] that
       synthesise the missing two on every use.  For [ULift.rec] at scheme
       j = 2*i (motive non-SProp), Lean also provides [motive] as the first
       universe, shifting [r] and [s] to positions 1 and 2 in [Level.var].
       For [ULift.rec] at j = 2*i+1 (motive SProp), [motive] is filtered
       out by [int_of_univs] so the indices match the non-rec case. *)
    let algs_of r_idx s_idx =
      let r = Universe.make (Level.var r_idx) in
      let s = Universe.make (Level.var s_idx) in
      [ Universe.super s; Universe.sup (Universe.super r) (Universe.super s) ]
    in
    let algs_2 = algs_of 0 1 in
    let algs_rec = algs_of 1 2 in
    let ulift_ref = Rocqlib.lib_ref (cumul_reg n) in
    let inst = { ref = ulift_ref; algs = algs_2 } in
    let up = { ref = Rocqlib.lib_ref (cumul_reg (N.append n "up")); algs = algs_2 } in
    check_predeclared_ind ind i ~nparams:None ~ctors:[ up ] inst;
    add_declared n i inst;
    (* The export's constructor (Lean's [ULift.up]), bound to ULift_up_cumul. *)
    List.iter (fun (cname, _) -> add_declared cname i up) ctors;
    (* Register ULift.down *)
    let dname = N.append n "down" in
    add_declared dname i { ref = Rocqlib.lib_ref (cumul_reg dname); algs = algs_2 };
    (* Register eliminator (Type scheme at j=2*i, SProp scheme at j=2*i+1) *)
    let nrec = N.append n "rec" in
    let rec_base = cumul_reg nrec in
    add_declared nrec (2 * i) { ref = Rocqlib.lib_ref rec_base; algs = algs_rec };
    add_declared nrec ((2 * i) + 1) { ref = Rocqlib.lib_ref (rec_base ^ ".ind"); algs = algs_2 };
    inst
  | None ->
  let uint32_is_legacy =
    let uname = N.append_list N.anon [ "UInt32" ] in
    match N.Map.find_opt uname !declared with
    | None -> false
    | Some m ->
      (match (Int.Map.find_opt 0 m, Rocqlib.lib_ref_opt "lean.UInt32.legacy") with
       | Some { ref = uint32_ref; _ }, Some legacy_ref ->
         Names.GlobRef.CanOrd.equal uint32_ref legacy_ref
       | _ -> false)
  in
  (* Check the entry against the predeclared [mind] the importer binds it to. *)
  let check_predeclared_mind mind =
    let mib = Global.lookup_mind mind in
    let pred_ctors =
      List.init (Array.length mib.mind_packets.(0).mind_consnames) (fun k ->
          { ref = GlobRef.ConstructRef ((mind, 0), k + 1); algs = [] })
    in
    check_predeclared_ind ind i ~nparams:(Some mib.mind_nparams) ~ctors:pred_ctors
      { ref = GlobRef.IndRef (mind, 0); algs = [] }
  in
  (* The export's constructors, bound in order to those of the inductive type. *)
  let cnames = List.map fst ctors in
  let mind, algs, ind_name, univs, squashy =
    match get_predeclared_ind_some ~ctors ~uint32_is_legacy n i with
    | Some (Eq, _, (ind_name, mind)) ->
      (* Hack to let the user predeclare eq and quot before running Lean Import
         TODO make a more general Register-like API? *)
      Feedback.msg_info Pp.(Id.print ind_name ++ str " is predeclared");
      check_predeclared_mind mind;
      let squashy =
        { maybe_prop = true; always_prop = true; lean_squashes = false }
      in
      let univs =
        match i with
        | 0 ->
          UContext.make
            { quals = [||]; univs =  [| Name (Id.of_string "u") |]}
            ( Instance.of_array ([||], [| univ_of_name (N.append N.anon "u") |]),
              PConstraints.empty )
        | 1 -> UContext.empty
        | _ -> assert false
      in
      (mind, [], ind_name, univs, squashy)
    | Some
        ( (Nat | Nat_le | Or | And | Fin | UInt32 | BitVec | Char),
          _,
          (ind_name, mind) ) ->
      (* Hack to let the user predeclare various types before running Lean Import
         TODO make a more general Register-like API? *)
      (* this case is for the ones without universes*)
      Feedback.msg_info Pp.(Id.print ind_name ++ str " is predeclared");
      check_predeclared_mind mind;
      let squashy = N.Map.get n !squash_info in
      (mind, [], ind_name, UContext.empty, squashy)
    | None ->
      let uconv = start_uconv univs i in
      let ( uconv,
            {
              tr_params = params;
              tr_arity = ty;
              tr_indices = indices;
              tr_sort = sort;
              tr_ctor_env = env_ind_params;
              tr_ctors;
            } ) =
        translate_ind uconv ind
      in
      let ctys = List.map snd tr_ctors in
      let graph = uconv.graph in
      let univs, algs = univ_entry_gen uconv univs in
      let ind_name = name_for n i in
      let record, fields, ctys =
        match (indices, ctys) with
        | [], [ cty ] ->
          cty
          |> with_env_evm env_ind_params uconv (fun env evm cty ->
                 let fields, codom =
                   Reductionops.whd_decompose_prod env evm
                     (EConstr.of_constr cty)
                 in
                 let _, fields =
                   CList.fold_left_map
                     (fun ids (na, t) ->
                       match na.Context.binder_name with
                       | Names.Anonymous -> (ids, (na, t))
                       | Names.Name id ->
                         let id = Namegen.next_global_ident_away (Global.safe_env ()) id ids in
                         let ids = Id.Set.add id ids in
                         line_msg
                           (N.of_list
                              [
                                Names.Id.to_string id;
                                "(field)";
                                Names.Id.to_string ind_name;
                              ]);
                         (ids, ({ na with binder_name = Names.Name id }, t)))
                     (Id.Set.add ind_name Id.Set.empty)
                     fields
                 in
                 let cty' = EConstr.it_mkProd codom fields in
                 let cty' = EConstr.Unsafe.to_constr cty' in
                 (* A recursive single-constructor inductive cannot admit
                    eta, so the kernel rejects the primitive-record
                    encoding. Fall through to plain Inductive in that case. *)
                 let npars = List.length params in
                 let is_recursive =
                   let rec walk k c =
                     match Constr.kind c with
                     | Constr.Prod (_, t, body) ->
                       (not (Vars.noccurn k t)) || walk (k + 1) body
                     | _ -> false
                   in
                   walk (npars + 1) cty'
                 in
                 let has_relevant_field =
                   List.exists
                     (fun (na, _) ->
                       na.Context.binder_relevance
                       == EConstr.ERelevance.relevant)
                     fields
                 in
                 match (fields, Sorts.is_sprop sort, is_recursive) with
                 | [], true, _ -> (None, [], ctys)
                 | _ :: _, false, false ->
                   (* Rocq gives eta to a primitive record outside SProp
                      only when it has a relevant field (or when universe
                      checking is off, which the import never does), and the
                      eliminator it builds from the projections of a
                      primitive record needs eta. A record outside SProp
                      whose fields are all SProp is therefore declared as a
                      non-primitive record: its projections and eliminator
                      are matches. *)
                   ( Some
                       (if has_relevant_field then Some [| default_proj_id |]
                        else None),
                     fields,
                     [ cty' ] )
                 | [], false, _ -> (None, [], ctys)
                 | _ :: _, true, false ->
                   if not has_relevant_field then
                     (Some (Some [| default_proj_id |]), fields, [ cty' ])
                   else (None, [], ctys)
                 | _ :: _, _, true -> (None, [], ctys))
        | _ -> (None, [], ctys)
      in
      let entry finite =
        {
          Entries.mind_entry_params = params;
          mind_entry_record = record;
          mind_entry_finite = finite;
          mind_entry_inds =
            [
              {
                mind_entry_typename = ind_name;
                mind_entry_arity = ty;
                mind_entry_consnames = List.map (fun n -> name_for n i) cnames;
                mind_entry_lc = ctys;
              };
            ];
          mind_entry_private = None;
          mind_entry_universes = Polymorphic_ind_entry univs;
          mind_entry_variance = None;
        }
      in
      let squashy = N.Map.get n !squash_info in
      let coq_squashes =
        if squashy.maybe_prop then coq_squashes graph (entry Finite) else false
      in
      let mind =
        let act finite =
          DeclareInd.declare_mutual_inductive_with_eliminations (entry finite)
            (* the ubinders API is kind of shit here *)
            (UState.Polymorphic_entry UContext.empty, UnivNames.empty_binders)
            []
        in
        (* The type is declared [BiFinite] when the kernel accepts that (a
           non-recursive type), else [Finite]. A critical exception, such as
           the [Control.Timeout] of the Lean Entry Timeout, is not a refusal
           of [BiFinite]: it ends the entry. *)
        let act () =
          try act BiFinite with e when CErrors.noncritical e -> act Finite
        in
        if squashy.lean_squashes || not coq_squashes then act ()
        else with_unsafe_univs act ()
      in
      assert (
        squashy.lean_squashes
        || (Global.lookup_mind mind).mind_packets.(0).mind_squashed == None);
      (* Declare projections if the inductive is a record *)
      let () =
        match record with
        | Some ids ->
          let inhabitant_id = ind_name in
          let kind = Decls.StructureComponent in
          let proj_flags =
            List.map
              (fun _ ->
                {
                  Record.Data.pf_coercion = None;
                  pf_instance = None;
                  pf_canonical = false;
                })
              fields
          in
          let implfs = List.map (fun _ -> []) fields in
          let projs =
            RecordInternal.declare_projections (mind, 0) ~kind ~inhabitant_id
              proj_flags implfs
          in
          (* The kernel keeps no projections for a non-primitive record:
             register them as a structure, so that [to_constr] finds the
             projection constant of a Lean [Proj]. *)
          (match ids with
           | None ->
             RecordInternal.declare_structure_entry
               (Structures.Structure.make (Global.env ()) (mind, 0) projs)
           | Some _ -> ())
        | None -> ()
      in
      (mind, algs, ind_name, univs, squashy)
  in

  (* add ind and ctors to [declared] *)
  let inst = { ref = GlobRef.IndRef (mind, 0); algs } in
  let () = add_declared n i inst in
  let () =
    CList.iteri
      (fun cnum cname ->
        add_declared cname i
          { ref = GlobRef.ConstructRef ((mind, 0), cnum + 1); algs })
      cnames
  in

  (* elim *)
  let make_scheme fam =
    let u =
      if fam = SchemeSProp then LSProp
      else
        let u =
          if lean_fancy_univs () then
            let u = DirPath.make [ Id.of_string "motive"; lean_id ] in
            Level.(make (UGlobal.make u "" 0))
          else UnivGen.fresh_level ()
        in
        Level u
    in
    let env = Environ.push_context ~strict:true univs (Global.env ()) in
    let env =
      match u with
      | LSProp -> env
      | Level u ->
        Environ.push_context_set ~strict:false (Univ.ContextSet.singleton u) env
    in
    let inst, uentry =
      let inst = UContext.instance univs in
      let csts = UContext.constraints univs in
      let { quals = qnames; univs = unames} = UContext.names univs in
      let uentry =
        match u with
        | LSProp -> UState.Polymorphic_entry univs
        | Level u ->
          UState.Polymorphic_entry
            (UContext.make
               {quals = qnames; univs = Array.append [| Name (Id.of_string "motive") |] unames}
               ( Instance.of_array
                   ([||], Array.append [| u |] (snd (Instance.to_array inst))),
                 csts ))
      in
      (inst, uentry)
    in
    (* lean 4 change: always dep? was not squashy.always_prop*)
    (lean_scheme env ~dep:true mind inst u, uentry)
  in
  let nrec = N.append n "rec" in
  let elims =
    if squashy.lean_squashes then [ ("_indl", SchemeSProp) ]
    else [ ("_recl", SchemeType); ("_indl", SchemeSProp) ]
  in

  let declare_one_scheme (suffix, sort) =
    let id = Id.of_string (Id.to_string ind_name ^ suffix) in
    let body, uentry = make_scheme sort in
    let elim =
      quickdef ~name:id ~types:None
        ~univs:(uentry, UnivNames.empty_binders)
        body
      (* TODO implicits? *)
    in
    (* TODO AFAICT Lean reduces recursors eagerly, but ofc only when applied to a ctor
       Can we simulate that with strategy better than by leaving them at the default strat? *)
    let liftu l =
      let u =
        match Level.var_index l with
        | None -> Universe.make l (* Set *)
        | Some i -> Universe.make (Level.var (i + 1))
      in
      Some u
    in
    let algs =
      if sort = SchemeSProp then algs
      else List.map (UnivSubst.subst_univs_universe liftu) algs
    in
    let elim = { ref = elim; algs } in
    let j =
      if squashy.lean_squashes then i
      else if sort == SchemeType then 2 * i
      else (2 * i) + 1
    in
    add_declared nrec j elim
  in
  let () =
    List.iter
      (fun x ->
        try declare_one_scheme x
        with e when CErrors.noncritical e && error_mode e = Skip ->
          Feedback.msg_info Pp.(str "Skipping scheme"))
      elims
  in
  inst

(** Generate and add the squashy info *)
let squashify { name = n; params; ty; ctors; univs } =
  let uconvP =
    (* NB: if univs = [] this is just instantiation 0 *)
    start_uconv univs ((1 lsl List.length univs) - 1)
  in
  let (env_paramsP, uconvP), paramsP = to_params uconvP params in
  let uconvP, tyP = to_constr env_paramsP ty uconvP in
  let envP =
    Environ.push_rel_context paramsP
      (Environ.set_universes uconvP.graph (Global.env ()))
  in
  let _, sortP = Reduction.dest_arity envP tyP in
  if not (Sorts.is_sprop sortP) then noprop
  else
    let uconvT = start_uconv univs 0 in
    let (env_paramsT, uconvT), paramsT = to_params uconvT params in
    let uconvT, tyT = to_constr env_paramsT ty uconvT in
    let envT =
      Environ.set_rel_context_val env_paramsT
        (Environ.set_universes uconvT.graph (Global.env ()))
    in
    let _, sortT = Reduction.dest_arity envT tyT in
    let always_prop = Sorts.is_sprop sortT in
    match ctors with
    | [] -> { maybe_prop = true; always_prop; lean_squashes = false }
    | _ :: _ :: _ -> { maybe_prop = true; always_prop; lean_squashes = true }
    | [ (_, ctor) ] ->
      let envT =
        Context.Rel.fold_outside Environ.push_rel_context_val paramsT
          ~init:
            (Environ.push_rel_context_val
               (LocalAssum
                  ( Context.make_annot (N.to_name n)
                      (Sorts.relevance_of_sort sortT),
                    Term.it_mkProd_or_LetIn tyT paramsT ))
               empty_env)
      in
      let uconvT, ctorT = to_constr envT ctor uconvT in
      let envT =
        Environ.set_rel_context_val envT
          (Environ.set_universes uconvT.graph (Global.env ()))
      in
      let args, out = Reduction.whd_decompose_prod envT ctorT in
      let forced =
        (* NB dest_prod returns [out] in whnf *)
        let _, outargs = Constr.decompose_app out in
        Array.fold_left
          (fun forced arg ->
            match Constr.kind arg with
            | Rel i -> Int.Set.add i forced
            | _ -> forced)
          Int.Set.empty outargs
      in
      let sigma = Evd.from_env envT in
      let npars = List.length params in
      let nargs = List.length args in
      let lean_squashes, _, _ =
        Context.Rel.fold_outside
          (fun d (squashed, i, envT) ->
            let squashed =
              if squashed then true
              else if Int.Set.mem (nargs - i) forced then false
              else
                let t = RelDecl.get_type d in
                if not (Vars.noccurn (npars + i + 1) t) then
                  (* recursive argument *)
                  false
                else
                  not
                    (EConstr.ESorts.is_sprop sigma
                       (Retyping.get_sort_of envT sigma (EConstr.of_constr t)))
            in

            (squashed, i + 1, Environ.push_rel d envT))
          args ~init:(false, 0, envT)
      in
      (* TODO translate to use non recursively uniform params (fix extraction)*)
      { maybe_prop = true; always_prop; lean_squashes }

let squashify ind =
  let s = squashify ind in
  squash_info := N.Map.add ind.name s !squash_info

(* pairs of (name * number of univs) *)
let quots = [ ("", 1); ("mk", 1); ("lift", 2); ("ind", 1) ]

let declare_quot quot_name =
  let () =
    List.iter
      (fun (n, nunivs) ->
        let rec loop i =
          if i = 1 lsl nunivs then ()
          else
            let lean =
              if CString.is_empty n then quot_name else N.append quot_name n
            in
            let reg =
              "lean." ^ N.to_lean_string lean
              ^ if i = 0 then "" else "_inst" ^ string_of_int i
            in
            let ref = Rocqlib.lib_ref reg in
            let () = add_declared lean i { ref; algs = [] } in
            loop (i + 1)
        in
        loop 0)
      quots
  in
  Feedback.msg_info Pp.(str "quot registered")

let declare_quot quot_name =
  if Rocqlib.has_ref "lean.Quot" then declare_quot quot_name else raise MissingQuot

let { Goptions.get = just_parse } =
  Goptions.declare_bool_option_and_ref
    ~key:[ "Lean"; "Just"; "Parsing" ]
    ~value:false ()

(* with this off: best line 23000 in stdlib
   stack overflow

   update: got fixed by e9e637de26 (distinguish names foo.bar and foo_bar)
*)
let { Goptions.get = upfront_instances } =
  Goptions.declare_bool_option_and_ref
    ~key:[ "Lean"; "Upfront"; "Instantiation" ]
    ~value:false ()

let { Goptions.get = lazy_instances } =
  Goptions.declare_bool_option_and_ref
    ~key:[ "Lean"; "Lazy"; "Instantiation" ]
    ~value:false ()

let declare_instances act univs =
  let stop = if upfront_instances () then 1 lsl List.length univs else 1 in
  let rec loop i =
    if i = stop then ()
    else
      let () = act i in
      loop (i + 1)
  in
  if not (lazy_instances ()) then loop 0

let declare_def def =
  declare_instances (fun i -> ignore (declare_def def i)) def.univs

let declare_ax ax =
  declare_instances (fun i -> ignore (declare_ax ax i)) ax.univs

let declare_ind ind =
  let () = squashify ind in
  declare_instances (fun i -> ignore (declare_ind ind i)) ind.univs

let entry_name = function
| Quot name | Def { name } | Ax { name } | Ind { name } -> name

(* Whether [n] is bound by a row of the predeclared table that dispatches
   between two Rocq records ([get_predeclared_uint32], [get_predeclared_char]):
   on the legacy path, such an entry may legitimately be emitted twice, the
   second [#IND] flipping the dispatch to the other record, and it is declared
   again. Those rows apply on the legacy path only: on the new path a repeated
   [UInt32] or [Char] is a duplicate like any other entry. The answer comes
   from the rows alone: no registration is read, since which record the entry
   binds depends on its constructors, which [declare_ind] reads. *)
let is_predeclared_dispatch_name n =
  List.exists
    (function
      | (UInt32 | Char), _, _ -> true
      | (Eq | Nat | Nat_le | Or | And | Fin | BitVec), _, _ -> false)
    (get_predeclared_ind_any n 0)

(* Duplicate entries can occur when lean4export is invoked with multiple
   roots that share a transitive dependency: the shared declaration is
   emitted once per root. Without this guard, re-processing a second
   copy would declare a renamed parallel inductive/def and silently
   overwrite the Lean->Rocq map, corrupting downstream references. *)
let add_entry entry =
  let name = entry_name entry in
  match N.Map.find_opt name !entries with
  | Some _ when not (is_predeclared_dispatch_name name) ->
    Feedback.msg_warning
      Pp.(
        str "Skipping duplicate declaration for " ++ N.pp name
        ++ str " (already declared earlier in the export).")
  | _ ->
    let () =
      match entry with
      | Quot quot_name -> declare_quot quot_name
      | Def def -> declare_def def
      | Ax ax -> declare_ax ax
      | Ind ind -> declare_ind ind
    in
    entries := N.Map.add name { entry; path = !current_path } !entries

let rec is_arity = function
  | Sort _ -> true
  | Pi (_, _, _, b) -> is_arity b
  | _ -> false

let { Goptions.get = print_squashes } =
  Goptions.declare_bool_option_and_ref
    ~key:[ "Lean"; "Print"; "Squash"; "Info" ]
    ~value:false ()

type parser_state =
  | OldParser of LeanParse.parsing_state
  | NdjsonParser of LeanParseNdjson.parsing_state

type input_state = {
  pstate : parser_state;
  skips : int;
}

let pp_parser_state = function
  | OldParser state -> LeanParse.pp_state state
  | NdjsonParser state -> LeanParseNdjson.pp_state state

let finish state =
  let max_univs, cnt =
    N.Map.fold
      (fun _ { entry; _ } (m, cnt) ->
        match entry with
        | Ax { univs } | Def { univs } | Ind { univs } ->
          let l = List.length univs in
          (max m l, cnt + (1 lsl l))
        | Quot _ -> (max m 1, cnt + 2))
      !entries (0, 0)
  in
  let nonarities =
    N.Map.fold
      (fun _ { entry; _ } cnt ->
        match entry with
        | Ax _ | Def _ | Quot _ -> cnt
        | Ind ind -> if is_arity ind.ty then cnt else cnt + 1)
      !entries 0
  in
  let squashes =
    if not (print_squashes ()) then Pp.mt ()
    else
      N.Map.fold
        (fun n s pp -> Pp.(pp ++ fnl () ++ N.pp n ++ spc () ++ pp_squashy s))
        !squash_info
        Pp.(mt ())
  in
  Feedback.msg_info
    Pp.(
      fnl () ++ fnl () ++ str "Done!" ++ fnl () ++ str "- "
      ++ int (N.Map.cardinal !entries)
      ++ str " entries (" ++ int cnt ++ str " possible instances)"
      ++ (if N.Map.exists (fun _ { entry; _ } -> match entry with Quot _ -> true | _ -> false) !entries then
            str " (including quot)."
          else str ".")
      ++ fnl () ++
      pp_parser_state state.pstate ++
      (if state.skips > 0 then str "Skipped " ++ int state.skips ++ fnl ()
       else mt ())
      ++ str "Max universe instance length "
      ++ int max_univs ++ str "." ++ fnl () ++ int nonarities
      ++ str " inductives have non syntactically arity types."
      ++ squashes)

let prtime t0 t1 =
  let diff = System.time_difference t0 t1 in
  if diff > 1.0 then
    Feedback.msg_info
      Pp.(
        str "line " ++ int !lcnt ++ str " took "
        ++ System.fmt_time_difference t0 t1)

let timeout = ref None

let () =
  Goptions.declare_int_option
    {
      optdepr = None;
      optstage = Interp;
      optkey = [ "Lean"; "Line"; "Timeout" ];
      optread = (fun () -> !timeout);
      optwrite = (fun x -> timeout := x);
    }

exception TimedOut

(* Lean Entry Timeout: how many seconds declaring one entry may take, unset by
   default. An entry still being declared then is refused with
   [EntryTimedOut]. *)
let entry_timeout = ref None

let () =
  LeanNatTransport.declare_positive_int_option
    ~key:[ "Lean"; "Entry"; "Timeout" ] ~unit:"seconds" entry_timeout

(* Lean Entry Memory Limit: by how many GiB declaring one entry may grow the
   major heap above its size at the entry's start, unset by default. An entry
   that grows it more is stopped and refused with [EntryMemoryLimit] (see
   [watching_memory]). *)
let entry_memory_limit = ref None

let () =
  LeanNatTransport.declare_positive_int_option
    ~key:[ "Lean"; "Entry"; "Memory"; "Limit" ] ~unit:"GiB" entry_memory_limit

(* The refusals of an entry stopped by a limit: the limit, and the size of the
   major heap at the entry's start, in MiB. *)
exception EntryTimedOut of int * int
exception EntryMemoryLimit of int * int

let () =
  let heap_at_start mib = Pp.(str "; major heap at the entry's start: " ++ int mib ++ str " MiB") in
  CErrors.register_handler (function
    | EntryTimedOut (n, mib) ->
      Some Pp.(str "Timed out after " ++ int n ++ str " s (Lean Entry Timeout)" ++ heap_at_start mib)
    | EntryMemoryLimit (n, mib) ->
      Some
        Pp.(
          str "Memory limit of " ++ int n ++ str " GiB reached (Lean Entry Memory Limit)"
          ++ heap_at_start mib)
    | _ -> None)

(* The size of the major heap, in words. *)
let heap_words () = (Gc.quick_stat ()).Gc.heap_words

let words_per_mib = (1 lsl 20) / (Sys.word_size / 8)

(* [n] GiB in words, or [max_int] when that does not fit an [int]. *)
let gib_words n =
  let per_gib = 1024 * words_per_mib in
  if n > max_int / per_gib then max_int else n * per_gib

(* What [watching_memory] found while an entry was being declared. *)
type memory_watch = {
  mutable stopped_at : float option;
      (** when the heap was first found over the limit, in wall-clock seconds *)
  mutable raised : bool;  (** whether [watching_memory] raised [Sys.Break] *)
}

(* How often OCaml's memory profiler samples the allocations of an entry under
   a memory limit: once per about 800 KB allocated. *)
let memory_sampling_rate = 1e-5

(* A removed alarm: the value of a watch's alarm until the watch creates its
   own, so that storing that alarm allocates nothing (see [watching_memory]). *)
let no_alarm =
  let alarm = Gc.create_alarm ignore in
  Gc.delete_alarm alarm;
  alarm

(* [watching_memory ~limit ~start w f x] computes [f x], the declaration of an
   entry with a starting major heap of [start] words. It stops the entry
   once the heap has grown by more than [limit] words.

   The watch measures the net growth of the major heap, which the whole
   process shares, at the ends of major collections: a GC alarm, run at the
   end of each one, reads the heap's size. Once that has grown past the limit,
   the alarm records the time in [w.stopped_at] and does nothing else: it
   allocates nothing after that record and raises nothing. The entry stops at
   the next sampled allocation of its own thread (below), so it can pass its
   limit by what the heap grows until the next collection ends and then until
   that sample; no fixed bound holds.

   The entry is stopped with [Sys.Break], which [CErrors.noncritical] does not
   cover, so no [with e when CErrors.noncritical e] handler between the kernel
   and [do_input] swallows it. Rocq's own interrupt flag, [Control.interrupt],
   was not enough on Rocq 07e45e36 and OCaml 4.14.2. In one trial, an alarm set
   the flag when RLI434.boundedVal._proof_1 in dumps/lean434/memory_twice.ndjson
   grew the heap by 1 GiB, 5.0 s into the entry. The reduction in this case
   did not poll the flag. The entry ran to its 30 s timeout with 8151 MiB of
   heap growth and the flag still set.

   An allocation callback of OCaml's memory profiler, [Gc.Memprof], raises
   [Sys.Break] instead. After the mark, each sampled allocation of the
   declaring thread raises it until [f x] ends.
   Allocations of other threads are never interrupted, and [Control.interrupt]
   is neither set nor cleared. On the same toolchain, a 1 GiB limit stopped
   both proofs in the fixture. The first stopped in the same millisecond as
   the mark (4.968 s into the entry, heap 1344 MiB from 108 MiB). In a trial
   with a second thread allocating throughout, that thread was not interrupted.

   The importer never takes over or stops a profiler it did not start.
   If one is already active, or if [Gc.Memprof.start] fails for another
   reason, the importer refuses the entry before declaring it.

   The watch allocates everything it needs before it acquires the alarm and
   then the profiler, and one release covers every exit, an exception during
   that startup included. The release first disables both callbacks, then
   removes the alarm, then stops the profiler if this watch started it, so the
   alarm is gone even if stopping the profiler raises. The
   alarm is stored over [no_alarm] and the profiler marked as started right
   after each call returns, with no allocation in between, so no asynchronous
   exception can arrive between acquiring either and the release knowing of
   it. *)
let watching_memory ~limit ~start w f x =
  let owner = Thread.id (Thread.self ()) in
  let active = ref true in
  let alarm = ref no_alarm in
  let profiling = ref false in
  let check_heap () =
    if !active && Option.is_empty w.stopped_at && heap_words () - start > limit then
      w.stopped_at <- Some (Unix.gettimeofday ())
  in
  let stop _ =
    if !active && Option.has_some w.stopped_at && Thread.id (Thread.self ()) = owner then begin
      w.raised <- true;
      raise Sys.Break
    end
    else None
  in
  let tracker = { Gc.Memprof.null_tracker with Gc.Memprof.alloc_minor = stop; alloc_major = stop } in
  let release () =
    active := false;
    Gc.delete_alarm !alarm;
    if !profiling then begin
      profiling := false;
      Gc.Memprof.stop ()
    end
  in
  let watch () =
    alarm := Gc.create_alarm check_heap;
    (match ignore (Gc.Memprof.start ~sampling_rate:memory_sampling_rate ~callstack_size:0 tracker) with
    | () -> profiling := true
    | exception Failure msg ->
      CErrors.user_err
        Pp.(
          str "Lean Entry Memory Limit cannot watch this entry, which is not declared: OCaml's memory profiler (Gc.Memprof) did not start ("
          ++ str msg ++ str ")."));
    f x
  in
  match watch () with
  | v ->
    release ();
    v
  | exception e ->
    release ();
    Exninfo.iraise (Exninfo.capture e)

(* [in_time ~start_mib n f x] computes [f x] under the Lean Entry Timeout of
   [n] s; [start_mib] is the size of the major heap at the entry's start, in
   MiB, for the refusal. *)
let in_time ~start_mib n f x =
  match Control.timeout (float_of_int n) f x with
  | Ok v -> v
  | Error info -> Exninfo.iraise (EntryTimedOut (n, start_mib), info)

(* Keep an observed outer [Control.Timeout] or [Sys.Break] not raised by
   the watch. If asynchronous exceptions replace each other during unwinding,
   only the surviving exception is visible here. A [Sys.Break] from the
   watch does not show whether an independent interrupt also occurred. *)
let add_entry_limited entry =
  match (!entry_timeout, !entry_memory_limit) with
  | None, None -> add_entry entry
  | Some n, None -> in_time ~start_mib:(heap_words () / words_per_mib) n add_entry entry
  | timeout, Some gib ->
    let start = heap_words () in
    let start_mib = start / words_per_mib in
    let t0 = Unix.gettimeofday () in
    let w = { stopped_at = None; raised = false } in
    let watched = watching_memory ~limit:(gib_words gib) ~start w add_entry in
    let scoped_timer = ref None in
    let remaining () = (Unix.getitimer Unix.ITIMER_REAL).it_value in
    let declare () =
      match timeout with
      | None -> watched entry
      | Some n when Sys.os_type = "Unix" || Sys.os_type = "Cygwin" ->
        let before = Unix.gettimeofday () in
        let outer = remaining () in
        (* [Control.unix_timeout] leaves an earlier timer in place. Compare
           a lower bound on its deadline with an upper bound on the deadline
           inside the scope. If they overlap, do not infer timer ownership. *)
        in_time ~start_mib n
          (fun entry ->
            let left = remaining () in
            let deadline = Unix.gettimeofday () +. left in
            scoped_timer := Some (deadline, outer = 0. || deadline < before +. outer);
            watched entry)
          entry
      | Some n -> in_time ~start_mib n watched entry
    in
    (* The watch ends before [Control.timeout] restores a timer it replaced. *)
    let memory_limit_reached info = Exninfo.iraise (EntryMemoryLimit (gib, start_mib), info) in
    (match declare () with
    | () ->
      (* The limit was passed, but the entry ended before a sample stopped it. *)
      if Option.has_some w.stopped_at then memory_limit_reached Exninfo.null
    | exception e ->
      let ((e, info) as exn) = Exninfo.capture e in
      let deadline_passed at n =
        match !scoped_timer with
        | Some (deadline, _) -> at >= deadline
        | None -> at >= t0 +. float_of_int n
      in
      (match (w.stopped_at, e) with
      | None, _ -> Exninfo.iraise exn
      | Some at, EntryTimedOut (n, _) when deadline_passed at n -> Exninfo.iraise exn
      | Some _, Control.Timeout -> Exninfo.iraise exn
      | Some _, Sys.Break when not w.raised -> Exninfo.iraise exn
      | Some at, Sys.Break ->
        (* An allocation callback can replace an entry timeout with its break.
           Infer the earlier time limit only for a known entry timer. *)
        (match (timeout, !scoped_timer) with
        | Some n, Some (deadline, true) when at >= deadline ->
          Exninfo.iraise (EntryTimedOut (n, start_mib), info)
        | _ -> memory_limit_reached info)
      | Some _, _ -> memory_limit_reached info))

(* Parse the line [l]: for its metadata, names, levels and expressions only
   when [prefix], a line before the first line to import (see [import]); the
   old text format reads nothing from such a line. *)
let do_line ~prefix state l =
  let do_line () =
    match state.pstate with
    | OldParser _ when prefix -> (state, None)
    | OldParser pstate ->
      let pstate, oentry = LeanParse.do_line pstate ~lcnt:!lcnt l in
      ({ state with pstate = OldParser pstate }, oentry)
    | NdjsonParser pstate when prefix ->
      ({ state with pstate = NdjsonParser (LeanParseNdjson.do_prefix_line pstate ~lcnt:!lcnt l) }, None)
    | NdjsonParser pstate ->
      let pstate, oentry = LeanParseNdjson.do_line pstate ~lcnt:!lcnt l in
      ({ state with pstate = NdjsonParser pstate }, oentry)
  in
  match !timeout with
  | None -> do_line ()
  | Some t ->
    (match Control.timeout (float_of_int t) do_line () with
    | Ok v -> v
    | Error info -> Exninfo.iraise (TimedOut, info))

let do_line ~prefix state l =
  let t0 = System.get_time () in
  match do_line ~prefix state l with
  | state ->
    let t1 = System.get_time () in
    prtime t0 t1;
    state
  | exception e ->
    let e = Exninfo.capture e in
    (if fst e <> TimedOut then
       let t1 = System.get_time () in
       prtime t0 t1);
    Exninfo.iraise e

let before_from = function None -> false | Some from -> !lcnt < from
let freeze () = (Lib.Interp.freeze (), Summary.Interp.freeze_summaries ())

let unfreeze (lib, sum) =
  Lib.Interp.unfreeze lib;
  Summary.Interp.unfreeze_summaries sum

(* The refusal of the current line [l]: [name] is what the line declares, [e]
   why it is refused. *)
let refusal ~name l e =
  Pp.(
    str "Error at line " ++ int !lcnt ++ str " (for " ++ name ++ str ")"
    ++ str (": " ^ l)
    ++ fnl () ++ CErrors.iprint e)

(* The name of a refused line that declares no entry the parser read. *)
let line_name () = Pp.(str "line-" ++ int !lcnt)

(* Whether failing to parse a line refuses it. The Lean Line Timeout's
   [TimedOut] and the asynchronous exceptions (an outer [Timeout], an
   interrupt) end the import instead. *)
let refuses_line = function
  | TimedOut -> false
  | e -> not (CErrors.is_async e)

let rec do_input state ~from ~until ch =
  if until = Some !lcnt then begin
    close_in ch;
    finish state;
    state
  end
  else
    match input_line ch with
    | exception End_of_file ->
      close_in ch;
      finish state;
      if not (until = None) then CErrors.user_err Pp.(str "unexpected EOF!");
      state
    | l ->
      (match do_line ~prefix:(before_from from) state l with
      | exception LeanParseNdjson.Refused { state = pstate; entry; error } ->
        let name = match entry with Some n -> N.pp n | None -> line_name () in
        refuse { state with pstate = NdjsonParser pstate } ~from ~until ch
          (fst error) (refusal ~name l error)
      | exception LeanParse.Refused { state = pstate; error } ->
        refuse { state with pstate = OldParser pstate } ~from ~until ch
          (fst error) (refusal ~name:(line_name ()) l error)
      | exception e when refuses_line e ->
        let e = Exninfo.capture e in
        refuse state ~from ~until ch (fst e) (refusal ~name:(line_name ()) l e)
      | state, oentry ->
        (match (just_parse (), oentry) with
        | true, _ | false, None ->
          incr lcnt;
          do_input state ~from ~until ch
        | false, Some (Nota _) ->
          (* notations not yet implemented *)
          incr lcnt;
          do_input state ~from ~until ch
        | false, Some (Entry entry) ->
          (* The path (with the Lean version) the export's metadata gave before
             its first entry. *)
          current_path :=
            (match state.pstate with
            | OldParser _ -> LeanParseNdjson.Legacy
            | NdjsonParser pstate -> LeanParseNdjson.path pstate);
          (* freeze is actually pretty costly, so make sure we don't run it for non sideffect lines. *)
          let st = freeze () in
          (match add_entry_limited entry with
          | () ->
            incr lcnt;
            do_input state ~from ~until ch
          | exception e ->
            (* Every exception refuses the entry, an asynchronous one too: the
               Lean Entry Timeout reaches here as [EntryTimedOut], the Lean
               Entry Memory Limit as [EntryMemoryLimit], and an outer
               [Timeout] or an interrupt that fires while the entry is being
               declared refuses it like any other error (see Lean Error Mode
               in README.md). *)
            let e = Exninfo.capture e in
            let msg = refusal ~name:(N.pp (entry_name entry)) l e in
            unfreeze st;
            (* without this unfreeze, the global state.declared and the
               global env are out of sync *)
            (* An entry stopped by a limit can leave a large heap: compact it
               now that the entry's state is undone, so that the space it held
               is given back before the next entry. *)
            (match fst e with EntryTimedOut _ | EntryMemoryLimit _ -> Gc.compact () | _ -> ());
            refuse state ~from ~until ch (fst e) msg)))

(* The Error Mode's answer to the refusal [msg] of the current line, refused
   because of [exn]. *)
and refuse state ~from ~until ch exn msg =
  match error_mode exn with
  | Skip ->
    Feedback.msg_info Pp.(str "Skipping: " ++ msg);
    incr lcnt;
    do_input { state with skips = state.skips + 1 } ~from ~until ch
  | Stop ->
    close_in ch;
    finish state;
    Feedback.msg_info msg;
    state
  | Fail ->
    close_in ch;
    finish state;
    CErrors.user_err msg

let pstate = Summary.ref ~name:"lean-parse-state" LeanParse.empty_state

(* The importer's state as one library object: [import] adds it at the end of each import, and it is written in the
   .vo (Keep) and restored by [cache] when it is added and when the library is loaded. The Summary.refs it restores
   are frozen and unfrozen in memory only. rocqchk reads the object with the rest of the .vo, and its reader
   (checker/analyze.ml) reads no OCaml custom block (a Zarith value of 2^62 or more, an Int32, a Bigarray) and no
   float array: the tuple holds the text parser's state, [sets], [declared], [entries], [squash_info] and
   [height_cache], that is names (string lists), strings (a literal is one, [LeanExpr.Nat]), ints, bools, Rocq's
   Level, Universe and GlobRef values, and maps, sets, lists and ranges of these. *)
let lean_obj =
  let cache (pstatev, setsv, declaredv, entriesv, squash_infov, heightv) =
    pstate := pstatev;
    sets := setsv;
    declared := declaredv;
    entries := entriesv;
    squash_info := squash_infov;
    height_cache := heightv;
    ()
  in
  let open Libobject in
  declare_object
    {
      (default_object "LEAN-IMPORT-STATE") with
      cache_function = cache;
      load_function = (fun _ v -> cache v);
      classify_function = (fun _ -> Keep);
    }

let import ~from ~until f =
  lcnt := 1;
  let initial_pstate =
    let rec first_non_empty_line ch =
      match input_line ch with
      | l ->
        if String.trim l = "" then first_non_empty_line ch
        else Some l
      | exception End_of_file -> None
    in
    let ch = open_in f in
    match first_non_empty_line ch with
    | Some l ->
      close_in ch;
      if LeanParseNdjson.is_ndjson_line l then NdjsonParser LeanParseNdjson.empty_state
      else OldParser !pstate
    | None ->
      close_in ch;
      OldParser !pstate
    | exception e ->
      close_in_noerr ch;
      raise e
  in
  (* silence the definition messages from Coq. [do_input] closes [ch] where it
     ends; when it raises instead, [ch] is closed here. *)
  let ch = open_in f in
  let { pstate = pstatev } =
    match
      Flags.silently (fun () -> do_input { pstate = initial_pstate; skips = 0 } ~from ~until ch) ()
    with
    | state -> state
    | exception e ->
      let e = Exninfo.capture e in
      close_in_noerr ch;
      Exninfo.iraise e
  in
  let old_pstatev =
    match pstatev with OldParser pstatev -> pstatev | NdjsonParser _ -> !pstate
  in
  Lib.add_leaf (lean_obj (old_pstatev, !sets, !declared, !entries, !squash_info, !height_cache))
