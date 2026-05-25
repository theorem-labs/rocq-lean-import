open LeanExpr
module N = LeanName
module Json = Yojson.Safe
module RRange = LeanParse.RRange

type parsing_state = {
  names : N.t RRange.t;
  exprs : expr RRange.t;
  univs : U.t RRange.t;
  seen_meta : bool;
}

let empty_state =
  {
    names = RRange.singleton N.anon;
    exprs = RRange.empty;
    univs = RRange.singleton U.Prop;
    seen_meta = false;
  }

let is_ndjson_line l =
  let l = String.trim l in
  String.length l > 0 && l.[0] = '{'

let err ~lcnt msg =
  CErrors.user_err Pp.(str "NDJSON parse error at line " ++ int lcnt ++ str ": " ++ str msg)

let member name = function
  | `Assoc fields -> List.assoc_opt name fields
  | _ -> None

let require_member ~lcnt name json =
  match member name json with
  | Some v -> v
  | None -> err ~lcnt ("missing field " ^ name)

let require_string ~lcnt name json =
  match require_member ~lcnt name json with
  | `String s -> s
  | _ -> err ~lcnt ("field " ^ name ^ " must be a string")

let require_int ~lcnt name json =
  match require_member ~lcnt name json with
  | `Int i -> i
  | _ -> err ~lcnt ("field " ^ name ^ " must be an integer")

let require_bool ~lcnt name json =
  match require_member ~lcnt name json with
  | `Bool b -> b
  | _ -> err ~lcnt ("field " ^ name ^ " must be a boolean")

let require_list ~lcnt name json =
  match require_member ~lcnt name json with
  | `List xs -> xs
  | _ -> err ~lcnt ("field " ^ name ^ " must be an array")

let as_int ~lcnt = function
  | `Int i -> i
  | _ -> err ~lcnt "expected integer"

let get_name ~lcnt state i =
  try RRange.get state.names i
  with Not_found -> err ~lcnt ("unknown name id " ^ string_of_int i)

let get_expr ~lcnt state i =
  try RRange.get state.exprs i
  with Not_found -> err ~lcnt ("unknown expression id " ^ string_of_int i)

let get_univ ~lcnt state i =
  try RRange.get state.univs i
  with Not_found -> err ~lcnt ("unknown level id " ^ string_of_int i)

let expect_next ~lcnt kind expected actual =
  if expected <> actual then
    err
      ~lcnt
      (kind ^ " id " ^ string_of_int actual ^ " is not the next expected id "
     ^ string_of_int expected)

let binders ~lcnt = function
  | "default" -> NotImplicit
  | "implicit" -> Maximal
  | "strictImplicit" -> NonMaximal
  | "instImplicit" -> Typeclass
  | b -> err ~lcnt ("unknown Lean binderInfo " ^ b)

let parse_name ~lcnt state json =
  let next = require_int ~lcnt "in" json in
  expect_next ~lcnt "name" (RRange.length state.names) next;
  match (member "str" json, member "num" json) with
  | Some payload, None ->
    let pre = require_int ~lcnt "pre" payload in
    let str = require_string ~lcnt "str" payload in
    let base = get_name ~lcnt state pre in
    ({ state with names = RRange.append state.names (N.append base str) }, None)
  | None, Some payload ->
    let pre = require_int ~lcnt "pre" payload in
    let i = require_int ~lcnt "i" payload in
    let base = get_name ~lcnt state pre in
    ( {
        state with
        names = RRange.append state.names (N.raw_append base (string_of_int i));
      },
      None )
  | _ -> err ~lcnt "bad name record"

let parse_level ~lcnt state json =
  let next = require_int ~lcnt "il" json in
  expect_next ~lcnt "level" (RRange.length state.univs) next;
  match (member "succ" json, member "max" json, member "imax" json, member "param" json) with
  | Some (`Int base), None, None, None ->
    ({ state with univs = RRange.append state.univs (U.Succ (get_univ ~lcnt state base)) }, None)
  | None, Some (`List [ a; b ]), None, None ->
    ( {
        state with
        univs =
          RRange.append
            state.univs
            (U.Max (get_univ ~lcnt state (as_int ~lcnt a), get_univ ~lcnt state (as_int ~lcnt b)));
      },
      None )
  | None, None, Some (`List [ a; b ]), None ->
    ( {
        state with
        univs =
          RRange.append
            state.univs
            (U.IMax (get_univ ~lcnt state (as_int ~lcnt a), get_univ ~lcnt state (as_int ~lcnt b)));
      },
      None )
  | None, None, None, Some (`Int n) ->
    ({ state with univs = RRange.append state.univs (U.UNamed (get_name ~lcnt state n)) }, None)
  | _ -> err ~lcnt "bad level record"

let parse_nat_lit ~lcnt = function
  | `String n ->
    let n =
      try Z.of_string n
      with Invalid_argument _ | Failure _ -> err ~lcnt "bad natural literal"
    in
    if Z.sign n < 0 then err ~lcnt "natural literal must be non-negative";
    n
  | `Int n ->
    let n = Z.of_int n in
    if Z.sign n < 0 then err ~lcnt "natural literal must be non-negative";
    n
  | _ -> err ~lcnt "bad natural literal"

let parse_expr ~lcnt state json =
  let next = require_int ~lcnt "ie" json in
  expect_next ~lcnt "expression" (RRange.length state.exprs) next;
  let expr =
    match
      ( member "bvar" json,
        member "sort" json,
        member "const" json,
        member "app" json,
        member "lam" json,
        member "forallE" json,
        member "letE" json,
        member "proj" json,
        member "natVal" json,
        member "strVal" json,
        member "mdata" json )
    with
    | Some (`Int n), None, None, None, None, None, None, None, None, None, None -> Bound n
    | None, Some (`Int u), None, None, None, None, None, None, None, None, None ->
      Sort (get_univ ~lcnt state u)
    | None, None, Some payload, None, None, None, None, None, None, None, None ->
      let name = get_name ~lcnt state (require_int ~lcnt "name" payload) in
      let us =
        require_list ~lcnt "us" payload
        |> List.map (fun u -> get_univ ~lcnt state (as_int ~lcnt u))
      in
      Const (name, us)
    | None, None, None, Some payload, None, None, None, None, None, None, None ->
      App
        ( get_expr ~lcnt state (require_int ~lcnt "fn" payload),
          get_expr ~lcnt state (require_int ~lcnt "arg" payload) )
    | None, None, None, None, Some payload, None, None, None, None, None, None ->
      Lam
        ( binders ~lcnt (require_string ~lcnt "binderInfo" payload),
          get_name ~lcnt state (require_int ~lcnt "name" payload),
          get_expr ~lcnt state (require_int ~lcnt "type" payload),
          get_expr ~lcnt state (require_int ~lcnt "body" payload) )
    | None, None, None, None, None, Some payload, None, None, None, None, None ->
      Pi
        ( binders ~lcnt (require_string ~lcnt "binderInfo" payload),
          get_name ~lcnt state (require_int ~lcnt "name" payload),
          get_expr ~lcnt state (require_int ~lcnt "type" payload),
          get_expr ~lcnt state (require_int ~lcnt "body" payload) )
    | None, None, None, None, None, None, Some payload, None, None, None, None ->
      Let
        {
          name = get_name ~lcnt state (require_int ~lcnt "name" payload);
          ty = get_expr ~lcnt state (require_int ~lcnt "type" payload);
          v = get_expr ~lcnt state (require_int ~lcnt "value" payload);
          rest = get_expr ~lcnt state (require_int ~lcnt "body" payload);
        }
    | None, None, None, None, None, None, None, Some payload, None, None, None ->
      Proj
        ( get_name ~lcnt state (require_int ~lcnt "typeName" payload),
          require_int ~lcnt "idx" payload,
          get_expr ~lcnt state (require_int ~lcnt "struct" payload) )
    | None, None, None, None, None, None, None, None, Some n, None, None ->
      Nat (parse_nat_lit ~lcnt n)
    | None, None, None, None, None, None, None, None, None, Some (`String s), None ->
      String s
    | None, None, None, None, None, None, None, None, None, None, Some payload ->
      get_expr ~lcnt state (require_int ~lcnt "expr" payload)
    | _ -> err ~lcnt "bad expression record"
  in
  ({ state with exprs = RRange.append state.exprs expr }, None)

let level_params ~lcnt state payload =
  require_list ~lcnt "levelParams" payload
  |> List.map (fun n -> get_name ~lcnt state (as_int ~lcnt n))

let line_msg ~lcnt name =
  Feedback.msg_info Pp.(str "line " ++ int lcnt ++ str ": " ++ N.pp name)

let parse_axiom ~lcnt state payload =
  ignore (require_bool ~lcnt "isUnsafe" payload);
  let name = get_name ~lcnt state (require_int ~lcnt "name" payload) in
  line_msg ~lcnt name;
  let ty = get_expr ~lcnt state (require_int ~lcnt "type" payload) in
  let univs = level_params ~lcnt state payload in
  (state, Some (Entry (Ax { name; ty; univs })))

let parse_deflike ~lcnt state payload =
  ignore (require_bool ~lcnt "isUnsafe" payload);
  let name = get_name ~lcnt state (require_int ~lcnt "name" payload) in
  line_msg ~lcnt name;
  let ty = get_expr ~lcnt state (require_int ~lcnt "type" payload) in
  let body = get_expr ~lcnt state (require_int ~lcnt "value" payload) in
  let univs = level_params ~lcnt state payload in
  (state, Some (Entry (Def { name; ty; body; univs })))

let parse_quot ~lcnt state payload =
  ignore (require_string ~lcnt "kind" payload);
  line_msg ~lcnt LeanParse.quot_name;
  (state, Some (Entry (Quot LeanParse.quot_name)))

let parse_ctor_val ~lcnt state ctor_json =
  let name = get_name ~lcnt state (require_int ~lcnt "name" ctor_json) in
  let ty = get_expr ~lcnt state (require_int ~lcnt "type" ctor_json) in
  (name, ty)

let parse_ind_param_shape ~lcnt f =
  try f ()
  with Assert_failure _ ->
    err ~lcnt "inductive parameter count does not match exported type"

let parse_ind_val ~lcnt state ind_json ctor_jsons =
  let name = get_name ~lcnt state (require_int ~lcnt "name" ind_json) in
  line_msg ~lcnt name;
  let nparams = require_int ~lcnt "numParams" ind_json in
  let ty0 = get_expr ~lcnt state (require_int ~lcnt "type" ind_json) in
  let params, ty =
    parse_ind_param_shape ~lcnt (fun () -> LeanParse.pop_params nparams ty0)
  in
  let ctors =
    ctor_jsons
    |> List.map (parse_ctor_val ~lcnt state)
    |> List.map (fun (ctor_name, ctor_ty) ->
      (ctor_name, parse_ind_param_shape ~lcnt (fun () ->
        LeanParse.fix_ctor name nparams ctor_ty)))
  in
  let univs = level_params ~lcnt state ind_json in
  Entry (Ind { name; params; ty; ctors; univs })

let parse_inductive ~lcnt state payload =
  let types = require_list ~lcnt "types" payload in
  let ctors = require_list ~lcnt "ctors" payload in
  match types with
  | [ ind_json ] -> (state, Some (parse_ind_val ~lcnt state ind_json ctors))
  | _ -> err ~lcnt "mutual inductive groups are not supported by the current importer model"

let parse_meta ~lcnt state json =
  let meta = require_member ~lcnt "meta" json in
  let format = require_member ~lcnt "format" meta in
  let version = require_string ~lcnt "version" format in
  if version <> "3.1.0" then err ~lcnt ("unsupported export format " ^ version);
  ({ state with seen_meta = true }, None)

let do_line ~lcnt state l =
  let l = String.trim l in
  if l = "" then (state, None)
  else
    let json =
      try Json.from_string l
      with Yojson.Json_error msg -> err ~lcnt msg
    in
    match member "meta" json with
    | Some _ -> parse_meta ~lcnt state json
    | None when not state.seen_meta -> err ~lcnt "expected metadata object before export records"
    | None -> (
      match
        ( member "str" json,
          member "num" json,
          member "succ" json,
          member "max" json,
          member "imax" json,
          member "param" json,
          member "ie" json,
          member "axiom" json,
          member "def" json,
          member "thm" json,
          member "opaque" json,
          member "quot" json,
          member "inductive" json )
      with
      | Some _, None, None, None, None, None, None, None, None, None, None, None, None
      | None, Some _, None, None, None, None, None, None, None, None, None, None, None ->
        parse_name ~lcnt state json
      | None, None, Some _, None, None, None, None, None, None, None, None, None, None
      | None, None, None, Some _, None, None, None, None, None, None, None, None, None
      | None, None, None, None, Some _, None, None, None, None, None, None, None, None
      | None, None, None, None, None, Some _, None, None, None, None, None, None, None ->
        parse_level ~lcnt state json
      | None, None, None, None, None, None, Some _, None, None, None, None, None, None ->
        parse_expr ~lcnt state json
      | None, None, None, None, None, None, None, Some payload, None, None, None, None, None ->
        parse_axiom ~lcnt state payload
      | None, None, None, None, None, None, None, None, Some payload, None, None, None, None
      | None, None, None, None, None, None, None, None, None, Some payload, None, None, None
      | None, None, None, None, None, None, None, None, None, None, Some payload, None, None ->
        parse_deflike ~lcnt state payload
      | None, None, None, None, None, None, None, None, None, None, None, Some payload, None ->
        parse_quot ~lcnt state payload
      | None, None, None, None, None, None, None, None, None, None, None, None, Some payload ->
        parse_inductive ~lcnt state payload
      | _ -> err ~lcnt "unsupported NDJSON record")

let pp_state state =
  let open Pp in
  str "- " ++ int (RRange.length state.univs) ++ str " universe expressions" ++ fnl () ++
  str "- " ++ int (RRange.length state.names) ++ str " names" ++ fnl () ++
  str "- " ++ int (RRange.length state.exprs) ++ str " expression nodes" ++ fnl ()
