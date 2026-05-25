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
      with Json.Json_error msg -> err ~lcnt msg
    in
    match member "meta" json with
    | Some _ -> parse_meta ~lcnt state json
    | None when not state.seen_meta -> err ~lcnt "expected metadata object before export records"
    | None -> err ~lcnt "unsupported NDJSON record"

let pp_state state =
  let open Pp in
  str "- " ++ int (RRange.length state.univs) ++ str " universe expressions" ++ fnl () ++
  str "- " ++ int (RRange.length state.names) ++ str " names" ++ fnl () ++
  str "- " ++ int (RRange.length state.exprs) ++ str " expression nodes" ++ fnl ()
