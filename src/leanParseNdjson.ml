open LeanExpr
module N = LeanName
module Json = Yojson.Safe
module RRange = LeanParseShared.RRange

type path = Legacy | New of (int * int * int)

type parsing_state = {
  names : N.t RRange.t;
  exprs : expr RRange.t;
  univs : U.t RRange.t;
  (* The ids of refused lines: each holds a placeholder in its range. *)
  refused_names : Int.Set.t;
  refused_exprs : Int.Set.t;
  refused_univs : Int.Set.t;
  seen_meta : bool;
  (* The path the first metadata line chose (see [export_path]). *)
  path : path;
}

let empty_state =
  {
    names = RRange.singleton N.anon;
    exprs = RRange.empty;
    univs = RRange.singleton U.Prop;
    refused_names = Int.Set.empty;
    refused_exprs = Int.Set.empty;
    refused_univs = Int.Set.empty;
    seen_meta = false;
    path = Legacy;
  }

let path state = state.path

exception Refused of {
  state : parsing_state;
  entry : N.t option;
  error : Exninfo.iexn;
}

(* [refusing ~state ~entry f] runs [f], which parses (part of) a line. A
   failure of [f] refuses the line: it raises [Refused] with [state ()] and
   [entry]. A [Refused] from [f] passes unchanged, and so does an asynchronous
   exception (an interrupt, a timeout), which ends the import instead. *)
let refusing ~state ~entry f =
  try f () with
  | Refused _ as e -> raise e
  | e when not (CErrors.is_async e) ->
    let e = Exninfo.capture e in
    raise (Refused { state = state (); entry; error = e })

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
  | None -> err ~lcnt ("no field " ^ name)

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

let forbid_member ~lcnt name json =
  match member name json with
  | Some _ -> err ~lcnt ("unexpected field " ^ name)
  | None -> ()

let require_list ~lcnt name json =
  match require_member ~lcnt name json with
  | `List xs -> xs
  | _ -> err ~lcnt ("field " ^ name ^ " must be an array")

let as_int ~lcnt = function
  | `Int i -> i
  | _ -> err ~lcnt "expected integer"

(* Export records are tagged unions: an index field plus exactly one "kind"
   key carrying the payload.  [tagged] returns that single key and its payload,
   rejecting records that carry none of [keys] (or more than one). *)
let tagged ~lcnt ~what keys json =
  match
    List.filter_map
      (fun k -> match member k json with Some v -> Some (k, v) | None -> None)
      keys
  with
  | [ tag ] -> tag
  | _ -> err ~lcnt ("bad " ^ what ^ " record")

let get ~lcnt kind range refused i =
  if Int.Set.mem i refused then
    err ~lcnt ("uses " ^ kind ^ " id " ^ string_of_int i ^ " of a refused line")
  else
    try RRange.get range i
    with Not_found -> err ~lcnt ("unknown " ^ kind ^ " id " ^ string_of_int i)

let get_name ~lcnt state i = get ~lcnt "name" state.names state.refused_names i
let get_expr ~lcnt state i = get ~lcnt "expression" state.exprs state.refused_exprs i
let get_univ ~lcnt state i = get ~lcnt "level" state.univs state.refused_univs i

(* The id fields of the numbered records: a name, level or expression record
   has one of them, once. *)
let id_keys = [ "in"; "il"; "ie" ]

let id_fields = function
  | `Assoc fields -> List.filter (fun (k, _) -> List.mem k id_keys) fields
  | _ -> []

let bad_next ~lcnt kind expected actual =
  err ~lcnt
    (kind ^ " id " ^ string_of_int actual ^ " is not the next expected id "
   ^ string_of_int expected)

let name_tags = [ "str"; "num" ]
let level_tags = [ "succ"; "max"; "imax"; "param" ]
let expr_tags =
  [ "bvar"; "sort"; "const"; "app"; "lam"; "forallE"; "letE"; "proj";
    "natVal"; "strVal"; "mdata" ]

(* [next_id ~placeholder f] parses with [f] the rest of a name, level or
   expression line whose id is the next one.  When [f] fails, the refusal
   carries [placeholder ()], the state with a stand-in for that id: the ids
   after it stay in sequence, and a line that uses it is refused in turn. *)
let next_id ~placeholder f = refusing ~state:placeholder ~entry:None f

let binders ~lcnt = function
  | "default" -> NotImplicit
  | "implicit" -> Maximal
  | "strictImplicit" -> NonMaximal
  | "instImplicit" -> Typeclass
  | b -> err ~lcnt ("unknown Lean binderInfo " ^ b)

let parse_name ~lcnt state next json =
  let placeholder () =
    { state with
      names = RRange.append state.names N.anon;
      refused_names = Int.Set.add next state.refused_names }
  in
  let base p = get_name ~lcnt state (require_int ~lcnt "pre" p) in
  let name =
    next_id ~placeholder (fun () ->
      match tagged ~lcnt ~what:"name" name_tags json with
      | "str", p -> N.append (base p) (require_string ~lcnt "str" p)
      | "num", p -> N.raw_append (base p) (string_of_int (require_int ~lcnt "i" p))
      | _ -> err ~lcnt "bad name record")
  in
  ({ state with names = RRange.append state.names name }, None)

let parse_level ~lcnt state next json =
  let placeholder () =
    { state with
      univs = RRange.append state.univs U.Prop;
      refused_univs = Int.Set.add next state.refused_univs }
  in
  let univ j = get_univ ~lcnt state (as_int ~lcnt j) in
  let level =
    next_id ~placeholder (fun () ->
      match tagged ~lcnt ~what:"level" level_tags json with
      | "succ", `Int base -> U.Succ (get_univ ~lcnt state base)
      | "max", `List [ a; b ] -> U.Max (univ a, univ b)
      | "imax", `List [ a; b ] -> U.IMax (univ a, univ b)
      | "param", `Int n -> U.UNamed (get_name ~lcnt state n)
      | _ -> err ~lcnt "bad level record")
  in
  ({ state with univs = RRange.append state.univs level }, None)

(* A natural literal ([LeanExpr.Nat]): a string of a number Zarith reads, or an integer; refused when negative.
   Kept as [Z.to_string] of its value, so that ["007"], ["7"] and [7] are the same string. *)
let parse_nat_lit ~lcnt json =
  let n =
    match json with
    | `String n -> (
      try Z.of_string n
      with Invalid_argument _ | Failure _ -> err ~lcnt "bad natural literal")
    | `Int n -> Z.of_int n
    | _ -> err ~lcnt "bad natural literal"
  in
  if Z.sign n < 0 then err ~lcnt "natural literal must be non-negative";
  Z.to_string n

let parse_expr ~lcnt state next json =
  let placeholder () =
    { state with
      exprs = RRange.append state.exprs (Bound 0);
      refused_exprs = Int.Set.add next state.refused_exprs }
  in
  let int_at p k = require_int ~lcnt k p in
  let name_at p k = get_name ~lcnt state (int_at p k) in
  let expr_at p k = get_expr ~lcnt state (int_at p k) in
  let abstraction p =
    ( binders ~lcnt (require_string ~lcnt "binderInfo" p),
      name_at p "name",
      expr_at p "type",
      expr_at p "body" )
  in
  let expr =
    next_id ~placeholder (fun () ->
      match tagged ~lcnt ~what:"expression" expr_tags json with
      | "bvar", `Int n -> Bound n
      | "sort", `Int u -> Sort (get_univ ~lcnt state u)
      | "const", p ->
        let us =
          require_list ~lcnt "us" p
          |> List.map (fun u -> get_univ ~lcnt state (as_int ~lcnt u))
        in
        Const (name_at p "name", us)
      | "app", p -> App (expr_at p "fn", expr_at p "arg")
      | "lam", p ->
        let bk, nm, ty, body = abstraction p in
        Lam (bk, nm, ty, body)
      | "forallE", p ->
        let bk, nm, ty, body = abstraction p in
        Pi (bk, nm, ty, body)
      | "letE", p ->
        Let
          {
            name = name_at p "name";
            ty = expr_at p "type";
            v = expr_at p "value";
            rest = expr_at p "body";
          }
      | "proj", p -> Proj (name_at p "typeName", int_at p "idx", expr_at p "struct")
      | "natVal", n -> Nat (parse_nat_lit ~lcnt n)
      | "strVal", `String s -> String s
      | "mdata", p -> expr_at p "expr"
      | _ -> err ~lcnt "bad expression record")
  in
  ({ state with exprs = RRange.append state.exprs expr }, None)

let level_params ~lcnt state payload =
  require_list ~lcnt "levelParams" payload
  |> List.map (fun n -> get_name ~lcnt state (as_int ~lcnt n))

let line_msg ~lcnt name =
  Feedback.msg_info Pp.(str "line " ++ int lcnt ++ str ": " ++ N.pp name)

(* [declaring ~lcnt state name f] announces the entry [name] of a declaration
   line, then parses the rest of the line with [f]: a refusal from [f] names
   the entry. *)
let declaring ~lcnt state name f =
  line_msg ~lcnt name;
  refusing ~state:(fun () -> state) ~entry:(Some name) f

let parse_axiom ~lcnt state payload =
  ignore (require_bool ~lcnt "isUnsafe" payload);
  let name = get_name ~lcnt state (require_int ~lcnt "name" payload) in
  declaring ~lcnt state name (fun () ->
    let ty = get_expr ~lcnt state (require_int ~lcnt "type" payload) in
    let univs = level_params ~lcnt state payload in
    (state, Some (Entry (Ax { name; ty; univs }))))

let require_reducibility_hint ~lcnt payload =
  match require_member ~lcnt "hints" payload with
  | `String ("opaque" | "abbrev") -> ()
  | `Assoc fields -> (
    match List.assoc_opt "regular" fields with
    | Some (`Int _) -> ()
    | _ -> err ~lcnt "field hints must be opaque, abbrev, or regular")
  | _ -> err ~lcnt "field hints must be opaque, abbrev, or regular"

let require_safety ~lcnt payload =
  match require_member ~lcnt "safety" payload with
  | `String ("unsafe" | "safe" | "partial") -> ()
  | _ -> err ~lcnt "field safety must be unsafe, safe, or partial"

let parse_deflike_common ~lcnt state payload =
  let name = get_name ~lcnt state (require_int ~lcnt "name" payload) in
  declaring ~lcnt state name (fun () ->
    let ty = get_expr ~lcnt state (require_int ~lcnt "type" payload) in
    let body = get_expr ~lcnt state (require_int ~lcnt "value" payload) in
    let univs = level_params ~lcnt state payload in
    (state, Some (Entry (Def { name; ty; body; univs }))))

let parse_def ~lcnt state payload =
  forbid_member ~lcnt "isUnsafe" payload;
  require_reducibility_hint ~lcnt payload;
  require_safety ~lcnt payload;
  ignore (require_list ~lcnt "all" payload);
  parse_deflike_common ~lcnt state payload

let parse_thm ~lcnt state payload =
  forbid_member ~lcnt "isUnsafe" payload;
  forbid_member ~lcnt "safety" payload;
  ignore (require_list ~lcnt "all" payload);
  parse_deflike_common ~lcnt state payload

let parse_opaque ~lcnt state payload =
  ignore (require_bool ~lcnt "isUnsafe" payload);
  ignore (require_list ~lcnt "all" payload);
  parse_deflike_common ~lcnt state payload

let parse_quot ~lcnt state payload =
  ignore (require_string ~lcnt "kind" payload);
  line_msg ~lcnt LeanParseShared.quot_name;
  (state, Some (Entry (Quot LeanParseShared.quot_name)))

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
  declaring ~lcnt state name (fun () ->
    let nparams = require_int ~lcnt "numParams" ind_json in
    let ty0 = get_expr ~lcnt state (require_int ~lcnt "type" ind_json) in
    let params, ty =
      parse_ind_param_shape ~lcnt (fun () -> LeanParseShared.pop_params nparams ty0)
    in
    let ctors =
      ctor_jsons
      |> List.map (parse_ctor_val ~lcnt state)
      |> List.map (fun (ctor_name, ctor_ty) ->
        (ctor_name, parse_ind_param_shape ~lcnt (fun () ->
          LeanParseShared.fix_ctor name nparams ctor_ty)))
    in
    let univs = level_params ~lcnt state ind_json in
    Entry (Ind { name; params; ty; ctors; univs }))

let parse_inductive ~lcnt state payload =
  let types = require_list ~lcnt "types" payload in
  let ctors = require_list ~lcnt "ctors" payload in
  match types with
  | [ ind_json ] -> (state, Some (parse_ind_val ~lcnt state ind_json ctors))
  | _ -> err ~lcnt "mutual inductive groups are not supported by the current importer model"

(* [MAJOR.MINOR.PATCH] at the start of [v], after one optional leading [v],
   followed by nothing or by a suffix after [-] ([4.17.0-rc1]). *)
let version_triple v =
  let v = if String.starts_with ~prefix:"v" v then String.sub v 1 (String.length v - 1) else v in
  let core = match String.index_opt v '-' with Some k -> String.sub v 0 k | None -> v in
  let number s =
    if s <> "" && String.for_all (fun c -> '0' <= c && c <= '9') s then int_of_string_opt s
    else None
  in
  match List.map number (String.split_on_char '.' core) with
  | [ Some major; Some minor; Some patch ] -> Some (major, minor, patch)
  | _ -> None

(* The path of an export, from its metadata [meta.lean.version]: Lean 4.17.0
   and later take the new path, with that version [MAJOR.MINOR.PATCH]; an
   earlier version takes the legacy one. A metadata object with no [lean]
   object, no [version] string, or a version that is not exactly three numbers
   before its first [-] (after one optional leading [v]; [4.17.0.1] is not)
   takes the legacy path, with a warning that names the field and its value. *)
let export_path ~lcnt meta =
  let legacy field value =
    Feedback.msg_warning
      Pp.(
        str "NDJSON metadata at line " ++ int lcnt ++ str ": field " ++ str field ++ str " is "
        ++ str value
        ++ str "; without a Lean version MAJOR.MINOR.PATCH in lean.version the export takes the legacy path.");
    Legacy
  in
  match member "lean" meta with
  | None -> legacy "lean" "absent"
  | Some (`Assoc _ as lean) -> (
    match member "version" lean with
    | None -> legacy "lean.version" "absent"
    | Some (`String v as value) -> (
      match version_triple v with
      | Some triple -> if triple >= (4, 17, 0) then New triple else Legacy
      | None -> legacy "lean.version" (Json.to_string value))
    | Some value -> legacy "lean.version" (Json.to_string value))
  | Some value -> legacy "lean" (Json.to_string value)

let parse_meta ~lcnt state json =
  let meta = require_member ~lcnt "meta" json in
  let format = require_member ~lcnt "format" meta in
  let format_version = require_string ~lcnt "version" format in
  if format_version <> "3.1.0" then err ~lcnt ("unsupported export format " ^ format_version);
  (* The first metadata line chooses the path, before the first entry. *)
  if state.seen_meta then (state, None)
  else
    ({ state with seen_meta = true; path = export_path ~lcnt meta }, None)

let declarations =
  [ ("axiom", parse_axiom);
    ("def", parse_def);
    ("thm", parse_thm);
    ("opaque", parse_opaque);
    ("quot", parse_quot);
    ("inductive", parse_inductive) ]

let has_tag tags json = List.exists (fun k -> member k json <> None) tags

let has_payload json =
  has_tag name_tags json || has_tag level_tags json || has_tag expr_tags json
  || has_tag ("meta" :: List.map fst declarations) json

let unsupported ~prefix ~lcnt state =
  if prefix then (state, None) else err ~lcnt "unsupported NDJSON record"

let bad_id ~prefix ~lcnt state json key kind expected =
  (* As before, an untagged name or level record with no clear next id is
     unsupported. A tagged record must report what is wrong with its id. *)
  if has_payload json then
    let actual = require_int ~lcnt key json in
    bad_next ~lcnt kind expected actual
  else unsupported ~prefix ~lcnt state

let parse_line ~prefix ~lcnt state l =
  let l = String.trim l in
  if l = "" then (state, None)
  else
    let json =
      try Json.from_string l
      with Yojson.Json_error msg -> err ~lcnt msg
    in
    match id_fields json with
    | [] when member "meta" json <> None -> parse_meta ~lcnt state json
    | _ when not state.seen_meta ->
      err ~lcnt "expected metadata object before export records"
    (* A clear next id chooses the sequence before the payload is read.
       A wrong or missing tag therefore refuses that id in its own sequence. *)
    | [ ("in", `Int i) ] when i = RRange.length state.names -> parse_name ~lcnt state i json
    | [ ("il", `Int i) ] when i = RRange.length state.univs -> parse_level ~lcnt state i json
    | [ ("ie", _) ] ->
      let i = require_int ~lcnt "ie" json in
      let expected = RRange.length state.exprs in
      if i <> expected then bad_next ~lcnt "expression" expected i;
      parse_expr ~lcnt state i json
    | [ ("in", _) ] ->
      bad_id ~prefix ~lcnt state json "in" "name" (RRange.length state.names)
    | [ ("il", _) ] ->
      bad_id ~prefix ~lcnt state json "il" "level" (RRange.length state.univs)
    | [] when has_tag name_tags json -> err ~lcnt "no field in"
    | [] when has_tag level_tags json -> err ~lcnt "no field il"
    | [] ->
      (* A prefix scan reads only the context, not the declarations. *)
      let declaration (k, parse) =
        match member k json with
        | Some payload ->
          Some (if prefix then (state, None) else parse ~lcnt state payload)
        | None -> None
      in
      (match List.find_map declaration declarations with
      | Some result -> result
      | None -> unsupported ~prefix ~lcnt state)
    | ids when has_payload json || List.mem_assoc "ie" ids ->
      err ~lcnt ("more than one id field: " ^ String.concat ", " (List.map fst ids))
    | _ -> unsupported ~prefix ~lcnt state

(* A line is refused with the state it was read with, except for a name, level
   or expression line, which leaves a placeholder for its id (see [next_id]). *)
let do_prefix_line ~lcnt state l =
  fst (refusing ~state:(fun () -> state) ~entry:None (fun () -> parse_line ~prefix:true ~lcnt state l))

let do_line ~lcnt state l =
  refusing ~state:(fun () -> state) ~entry:None (fun () -> parse_line ~prefix:false ~lcnt state l)

let pp_state state =
  let open Pp in
  str "- " ++ int (RRange.length state.univs) ++ str " universe expressions" ++ fnl () ++
  str "- " ++ int (RRange.length state.names) ++ str " names" ++ fnl () ++
  str "- " ++ int (RRange.length state.exprs) ++ str " expression nodes" ++ fnl ()
