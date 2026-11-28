open LeanExpr
module N = LeanName

module RRange = LeanParseShared.RRange

let do_bk = function
  | "#BD" -> NotImplicit
  | "#BI" -> Maximal
  | "#BS" -> NonMaximal
  | "#BC" -> Typeclass
  | bk ->
    CErrors.user_err
      Pp.(str "unknown binder kind " ++ str bk ++ str "." ++ fnl ())

let do_notation_kind = function
  | "#PREFIX" -> Prefix
  | "#INFIX" -> Infix
  | "#POSTFIX" -> Postfix
  | k -> assert false

type parsing_state = {
  names : N.t RRange.t;
  exprs : expr RRange.t;
  univs : U.t RRange.t;
  refused_names : Int.Set.t;
  refused_exprs : Int.Set.t;
  refused_univs : Int.Set.t;
}

let empty_state =
  {
    names = RRange.singleton N.anon;
    exprs = RRange.empty;
    univs = RRange.singleton U.Prop;
    refused_names = Int.Set.empty;
    refused_exprs = Int.Set.empty;
    refused_univs = Int.Set.empty;
  }

exception Refused of { state : parsing_state; error : Exninfo.iexn }

let get kind range refused id =
  let id = int_of_string id in
  if Int.Set.mem id refused then
    CErrors.user_err Pp.(str "uses " ++ str kind ++ spc () ++ int id ++ str " of a refused line");
  match RRange.get range id with
  | value -> value
  | exception Not_found ->
    CErrors.user_err Pp.(str "unknown " ++ str kind ++ spc () ++ int id)

let get_name state n = get "name" state.names state.refused_names n
let get_expr state e = get "expression" state.exprs state.refused_exprs e
let as_univ state u = get "level" state.univs state.refused_univs u

let rec do_ctors state nctors acc l =
  if nctors = 0 then (List.rev acc, l)
  else
    match l with
    | name :: ty :: rest ->
      let name = get_name state name
      and ty = get_expr state ty in
      do_ctors state (nctors - 1) ((name, ty) :: acc) rest
    | _ -> CErrors.user_err Pp.(str "Not enough constructors")

let pop_params = LeanParseShared.pop_params
let fix_ctor = LeanParseShared.fix_ctor

(* A byte of a string literal ([#ELS]) is two hexadecimal digits. The exports
   write them in upper case; lower case reads the same. *)
let parse_hexa s c =
  if '0' <= c && c <= '9' then Char.code c - Char.code '0'
  else if 'A' <= c && c <= 'F' then Char.code c - Char.code 'A' + 10
  else if 'a' <= c && c <= 'f' then Char.code c - Char.code 'a' + 10
  else CErrors.user_err Pp.(str "bad byte " ++ qstring s ++ str " in a string literal.")

let parse_char s =
  if String.length s <> 2 then
    CErrors.user_err Pp.(str "bad byte " ++ qstring s ++ str " in a string literal.");
  Char.chr ((parse_hexa s s.[0] * 16) + parse_hexa s s.[1])

let quot_name = LeanParseShared.quot_name

type sequence = Name | Level | Expr

let bad_line l =
  CErrors.user_err Pp.(str "cannot understand " ++ str l ++ str "." ++ fnl ())

let sequence l = function
  | ("#NS" | "#NI") :: _ -> Name
  | ("#US" | "#UM" | "#UIM" | "#UP") :: _ -> Level
  | ("#EV" | "#ES" | "#EC" | "#EA" | "#EZ" | "#EL" | "#EP" | "#EJ" | "#ELN" | "#ELS") :: _ ->
    Expr
  | _ -> bad_line l

let check_next label expected next =
  if next <> expected then
    CErrors.user_err
      Pp.(str label ++ spc () ++ int next ++ str " is not the next expected id " ++ int expected)

let expect_next state kind next =
  match kind with
  | Name -> check_next "name" (RRange.length state.names) next
  | Level -> check_next "level" (RRange.length state.univs) next
  | Expr -> check_next "expression" (RRange.length state.exprs) next

(* The placeholder advances the sequence. Lookups reject it by id. *)
let reserve state kind next =
  match kind with
  | Name ->
    { state with
      names = RRange.append state.names N.anon;
      refused_names = Int.Set.add next state.refused_names }
  | Level ->
    { state with
      univs = RRange.append state.univs U.Prop;
      refused_univs = Int.Set.add next state.refused_univs }
  | Expr ->
    { state with
      exprs = RRange.append state.exprs (Bound 0);
      refused_exprs = Int.Set.add next state.refused_exprs }

let numbered_payload state l = function
  | [ "#NS"; base; cons ] ->
    let base = get_name state base in
    let cons = N.append base cons in
    { state with names = RRange.append state.names cons }
  | [ "#NI"; base; cons ] ->
    (* NI: private name. cons is an int, base is expected to be _private :: stuff
       (true in lean stdlib, dunno elsewhere) *)
    let base = get_name state base in
    let n = N.raw_append base cons in
    { state with names = RRange.append state.names n }
  | [ "#US"; base ] ->
    let base = as_univ state base in
    { state with univs = RRange.append state.univs (Succ base) }
  | [ "#UM"; a; b ] ->
    let a = as_univ state a
    and b = as_univ state b in
    { state with univs = RRange.append state.univs (Max (a, b)) }
  | [ "#UIM"; a; b ] ->
    let a = as_univ state a
    and b = as_univ state b in
    { state with univs = RRange.append state.univs (IMax (a, b)) }
  | [ "#UP"; n ] ->
    let n = get_name state n in
    { state with univs = RRange.append state.univs (UNamed n) }
  | [ "#EV"; n ] ->
    let n = int_of_string n in
    { state with exprs = RRange.append state.exprs (Bound n) }
  | [ "#ES"; u ] ->
    let u = as_univ state u in
    { state with exprs = RRange.append state.exprs (Sort u) }
  | "#EC" :: n :: univs ->
    let n = get_name state n in
    let univs = List.map (as_univ state) univs in
    { state with exprs = RRange.append state.exprs (Const (n, univs)) }
  | [ "#EA"; a; b ] ->
    let a = get_expr state a
    and b = get_expr state b in
    { state with exprs = RRange.append state.exprs (App (a, b)) }
  | [ "#EZ"; n; ty; v; rest ] ->
    let n = get_name state n
    and ty = get_expr state ty
    and v = get_expr state v
    and rest = get_expr state rest in
    { state with exprs = RRange.append state.exprs (Let { name = n; ty; v; rest }) }
  | [ "#EL"; bk; n; ty; body ] ->
    let bk = do_bk bk
    and n = get_name state n
    and ty = get_expr state ty
    and body = get_expr state body in
    { state with exprs = RRange.append state.exprs (Lam (bk, n, ty, body)) }
  | [ "#EP"; bk; n; ty; body ] ->
    let bk = do_bk bk
    and n = get_name state n
    and ty = get_expr state ty
    and body = get_expr state body in
    { state with exprs = RRange.append state.exprs (Pi (bk, n, ty, body)) }
  | [ "#EJ"; ind; field; term ] ->
    let ind = get_name state ind
    and field = int_of_string field
    and term = get_expr state term in
    { state with exprs = RRange.append state.exprs (Proj (ind, field, term)) }
  | [ "#ELN"; n ] ->
    let n = LeanParseShared.nat_lit (Z.of_string n) in
    { state with exprs = RRange.append state.exprs n }
  | "#ELS" :: bytes ->
    let s = Seq.map parse_char (List.to_seq bytes) in
    let s = String.of_seq s in
    { state with exprs = RRange.append state.exprs (String s) }
  | _ -> bad_line l

let do_line ~lcnt state l =
  let line_msg name =
    Feedback.msg_info Pp.(str "line " ++ int lcnt ++ str ": " ++ N.pp name)
  in
  (* Lean printing strangeness: sometimes we get double spaces (typically with INFIX) *)
  match
    List.filter (fun s -> s <> "") (String.split_on_char ' ' (String.trim l))
  with
  | [] -> (state, None) (* empty line *)
  | "#DEF" :: name :: ty :: body :: univs ->
    let name = get_name state name in
    line_msg name;
    let ty = get_expr state ty
    and body = get_expr state body
    and univs = List.map (get_name state) univs in
    let def = { name; ty; body; univs; } in
    (state, Some (Entry (Def def)))
  | "#AX" :: name :: ty :: univs ->
    let name = get_name state name in
    line_msg name;
    let ty = get_expr state ty
    and univs = List.map (get_name state) univs in
    let ax = { name; ty; univs } in
    (state, Some (Entry (Ax ax)))
  | "#IND" :: nparams :: name :: ty :: nctors :: rest ->
    let name = get_name state name in
    line_msg name;
    let nparams = int_of_string nparams
    and ty = get_expr state ty
    and nctors = int_of_string nctors in
    let params, ty = pop_params nparams ty in
    let ctors, univs = do_ctors state nctors [] rest in
    let ctors =
      List.map (fun (nctor, ty) -> (nctor, fix_ctor name nparams ty)) ctors
    in
    let univs = List.map (get_name state) univs in
    let ind = { name; params; ty; ctors; univs } in
    (state, Some (Entry (Ind ind)))
  | [ "#QUOT" ] ->
    line_msg quot_name;
    (state, Some (Entry (Quot quot_name)))
  | (("#PREFIX" | "#INFIX" | "#POSTFIX") as kind) :: rest ->
    (match rest with
    | [ n; level; token ] ->
      let kind = do_notation_kind kind
      and n = get_name state n
      and level = int_of_string level in
      (state, Some (Nota { kind; head = n; level; token }))
    | _ ->
      CErrors.user_err
        Pp.(
          str "bad notation: " ++ prlist_with_sep (fun () -> str "; ") str rest))
  | next :: rest ->
    let next =
      try int_of_string next
      with Failure _ ->
        CErrors.user_err Pp.(str "Unknown start of line " ++ str next)
    in
    let kind = sequence l rest in
    expect_next state kind next;
    (match numbered_payload state l rest with
    | state -> (state, None)
    | exception e when not (CErrors.is_async e) ->
      let error = Exninfo.capture e in
      raise (Refused { state = reserve state kind next; error }))

let pp_state state =
  let open Pp in
  str "- " ++ int (RRange.length state.univs) ++ str " universe expressions" ++ fnl () ++
  str "- " ++ int (RRange.length state.names) ++ str " names" ++ fnl () ++
  str "- " ++ int (RRange.length state.exprs) ++ str " expression nodes" ++ fnl ()
