# Lean4export NDJSON Regeneration Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make `rocq-lean-import` consume current `lean4export` NDJSON dumps and provide a reproducible path to regenerate maintained fixtures from the `lean4export`-pinned Lean toolchain.

**Architecture:** Add an NDJSON parser frontend that maps current `lean4export` records into the existing `LeanExpr.action` model, then dispatch `Lean Import` to either the old parser or the new parser by detecting the first meaningful input line. Add a fixture manifest and regeneration script so upstream-backed and local Lean fixtures can be rebuilt without changing the translation core.

**Tech Stack:** OCaml, Rocq plugin APIs, Dune, `yojson`, Make, POSIX shell, Lean/Lake/Elan, `lean4export`.

---

## File Structure

- Modify `rocq-lean-import.opam`: add `yojson` as an OCaml dependency for NDJSON decoding.
- Modify `src/dune`: add `yojson` to the OCaml library dependencies.
- Modify `Makefile`: pass the `yojson` findlib package to the generated Rocq makefile build.
- Modify `src/lean_import.mlpack`: include the new parser module before `Lean`.
- Modify `_CoqProject`: include the new parser module sources so `rocq makefile` emits build rules.
- Modify `src/leanParse.mli`: expose parser helper types/functions shared by old and new parser modules.
- Modify `src/leanParse.ml`: expose `RRange`, `pop_params`, `fix_ctor`, and `quot_name` through the existing interface without changing old-format behavior.
- Create `src/leanParseNdjson.mli`: declare NDJSON parser state, format detection, line parsing, and state pretty-printing.
- Create `src/leanParseNdjson.ml`: decode Lean 4 export format `3.1.0` records into `LeanExpr.action`.
- Modify `src/lean.ml`: split input parsing by detected format, preserve old parser behavior, and route NDJSON lines through `LeanParseNdjson`.
- Create `tests/fixtures/ndjson/`: small checked-in NDJSON fixtures for parser and import tests.
- Create `tests/ndjson_smoke.v`: Rocq-level smoke test that imports a minimal NDJSON dump.
- Modify `tests/_CoqProject`: include `tests/ndjson_smoke.v`.
- Create `lean/fixtures/manifest.toml`: lock `lean4export` metadata and define maintained dump sources.
- Create local Lean fixture files under `lean/fixtures/`.
- Create `scripts/regenerate-dumps.sh`: build/run `lean4export` according to the manifest.
- Modify `Makefile`: add `regenerate-dumps` target.
- Modify `README.md`: document NDJSON support and dump regeneration.

## Task 1: Add JSON Dependency And A Minimal NDJSON Fixture

**Files:**
- Modify: `rocq-lean-import.opam`
- Modify: `src/dune`
- Create: `tests/fixtures/ndjson/minimal.ndjson`
- Test: `make`

- [ ] **Step 1: Add the OCaml JSON dependency to opam**

In `rocq-lean-import.opam`, add `"yojson"` to the `depends` list:

```opam
depends: [
  "ocaml" {>= "4.09.0"}
  "rocq-core" {>= "9.0~" | = "dev"}
  "rocq-stdlib"
  "yojson"
]
```

- [ ] **Step 2: Add the Dune library dependency**

In `src/dune`, change the library stanza to include `yojson`:

```lisp
(library
 (name lean_import)
 (synopsis "Import Lean proofs into Coq!")
 (libraries rocq-runtime.vernac yojson)
 (modules_without_implementation leanExpr)
 (flags :standard -w -40))
```

- [ ] **Step 3: Add the minimal NDJSON fixture**

Create `tests/fixtures/ndjson/minimal.ndjson`:

```json
{"meta":{"exporter":{"name":"lean4export","version":"test"},"lean":{"githash":"test","version":"v4.30.0-rc2"},"format":{"version":"3.1.0"}}}
{"str":{"pre":0,"str":"Nat"},"in":1}
{"str":{"pre":1,"str":"zero"},"in":2}
{"const":{"name":2,"us":[]},"ie":0}
{"axiom":{"name":2,"levelParams":[],"type":0,"isUnsafe":false}}
```

This fixture intentionally reuses `Nat.zero` as a trivial declaration name and type. It is parser-only input at this stage.

- [ ] **Step 4: Verify dependency wiring still builds**

Run:

```bash
make
```

Expected: the build either succeeds, or fails only because `yojson` is not installed in the current opam switch. If `yojson` is missing, install it with the project dependency workflow and rerun `make`.

- [ ] **Step 5: Commit dependency and fixture**

```bash
git add rocq-lean-import.opam src/dune tests/fixtures/ndjson/minimal.ndjson
git commit -m "build: add json parser dependency"
```

## Task 2: Expose Shared Parser Helpers

**Files:**
- Modify: `src/leanParse.mli`
- Modify: `src/leanParse.ml`
- Test: `make`

- [ ] **Step 1: Extend the parser interface**

Replace `src/leanParse.mli` with:

```ocaml
open LeanExpr

module RRange : sig
  type +'a t

  val empty : 'a t
  val length : 'a t -> int
  val append : 'a t -> 'a -> 'a t
  val get : 'a t -> int -> 'a
  val singleton : 'a -> 'a t
end

type parsing_state

val empty_state : parsing_state
val do_line : lcnt:int -> parsing_state -> string -> parsing_state * action option
val pp_state : parsing_state -> Pp.t

val pop_params : int -> expr -> (binder_kind * LeanName.t * expr) list * expr
val fix_ctor : LeanName.t -> int -> expr -> expr
val quot_name : LeanName.t
```

- [ ] **Step 2: Confirm old parser definitions already match the interface**

Run this command:

```bash
rg -n 'module RRange|let rec pop_params|let fix_ctor|let quot_name' src/leanParse.ml
```

Expected output includes one top-level definition for each exported helper.
No behavior change is needed in `src/leanParse.ml` if those definitions remain
top-level.

- [ ] **Step 3: Run the build**

Run:

```bash
make
```

Expected: PASS with the old parser still compiling.

- [ ] **Step 4: Commit the parser interface change**

```bash
git add src/leanParse.mli src/leanParse.ml
git commit -m "refactor: expose lean parser helpers"
```

## Task 3: Add The NDJSON Parser Skeleton And Format Metadata Handling

**Files:**
- Modify: `Makefile`
- Modify: `_CoqProject`
- Modify: `src/lean_import.mlpack`
- Create: `src/leanParseNdjson.mli`
- Create: `src/leanParseNdjson.ml`
- Test: `make`

- [ ] **Step 1: Add the new module to the mlpack**

Change `src/lean_import.mlpack` to:

```text
LeanName
LeanParse
LeanParseNdjson
Lean
G_lean
```

- [ ] **Step 2: Pass Yojson to the generated Rocq makefile build**

Change `Makefile` so the submake invocation passes the Yojson findlib package:

```make
CAMLPKGS ?= -package yojson

submake: Makefile.rocq
	$(MAKE) $(MAKE_OPTS) -f Makefile.rocq CAMLPKGS="$(CAMLPKGS)" $(filter-out test%, $(MAKECMDGOALS))
```

- [ ] **Step 3: Add the new module to `_CoqProject`**

Add the new parser sources near the other parser/source files:

```text
src/leanParseNdjson.ml
src/leanParseNdjson.mli
```

- [ ] **Step 4: Create the NDJSON parser interface**

Create `src/leanParseNdjson.mli`:

```ocaml
open LeanExpr

type parsing_state

val empty_state : parsing_state
val is_ndjson_line : string -> bool
val do_line : lcnt:int -> parsing_state -> string -> parsing_state * action option
val pp_state : parsing_state -> Pp.t
```

- [ ] **Step 5: Create the parser skeleton**

Create `src/leanParseNdjson.ml`:

```ocaml
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
      with Yojson.Json_error msg -> err ~lcnt msg
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
```

- [ ] **Step 6: Run the build**

Run:

```bash
make
```

Expected: PASS, with the new parser module compiled but not yet used by `Lean Import`.

- [ ] **Step 7: Commit the skeleton**

```bash
git add Makefile _CoqProject src/lean_import.mlpack src/leanParseNdjson.mli src/leanParseNdjson.ml
git commit -m "feat: add ndjson parser skeleton"
```

## Task 4: Implement NDJSON Names, Levels, Expressions, And Basic Declarations

**Files:**
- Modify: `src/leanParseNdjson.ml`
- Test: `make`

- [ ] **Step 1: Add table access and JSON conversion helpers**

In `src/leanParseNdjson.ml`, add these helpers after `require_string`:

```ocaml
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
  try RRange.get state.names i with Not_found -> err ~lcnt ("unknown name id " ^ string_of_int i)

let get_expr ~lcnt state i =
  try RRange.get state.exprs i with Not_found -> err ~lcnt ("unknown expression id " ^ string_of_int i)

let get_univ ~lcnt state i =
  try RRange.get state.univs i with Not_found -> err ~lcnt ("unknown level id " ^ string_of_int i)

let expect_next ~lcnt kind expected actual =
  if expected <> actual then
    err ~lcnt (kind ^ " id " ^ string_of_int actual ^ " is not the next expected id " ^ string_of_int expected)

let binders = function
  | "default" -> NotImplicit
  | "implicit" -> Maximal
  | "strictImplicit" -> NonMaximal
  | "instImplicit" -> Typeclass
  | b -> CErrors.user_err Pp.(str "unknown Lean binderInfo " ++ str b)
```

- [ ] **Step 2: Implement name and level records**

Add these functions after the helper block:

```ocaml
let parse_name ~lcnt state json =
  match (member "str" json, member "num" json) with
  | Some payload, None ->
    let next = require_int ~lcnt "in" json in
    expect_next ~lcnt "name" (RRange.length state.names) next;
    let pre = require_int ~lcnt "pre" payload in
    let str = require_string ~lcnt "str" payload in
    let base = get_name ~lcnt state pre in
    ({ state with names = RRange.append state.names (N.append base str) }, None)
  | None, Some payload ->
    let next = require_int ~lcnt "in" json in
    expect_next ~lcnt "name" (RRange.length state.names) next;
    let pre = require_int ~lcnt "pre" payload in
    let i = require_int ~lcnt "i" payload in
    let base = get_name ~lcnt state pre in
    ({ state with names = RRange.append state.names (N.raw_append base (string_of_int i)) }, None)
  | _ -> err ~lcnt "bad name record"

let parse_level ~lcnt state json =
  let next = require_int ~lcnt "il" json in
  expect_next ~lcnt "level" (RRange.length state.univs) next;
  match (member "succ" json, member "max" json, member "imax" json, member "param" json) with
  | Some (`Int base), None, None, None ->
    ({ state with univs = RRange.append state.univs (U.Succ (get_univ ~lcnt state base)) }, None)
  | None, Some (`List [ a; b ]), None, None ->
    ({ state with univs = RRange.append state.univs (U.Max (get_univ ~lcnt state (as_int ~lcnt a), get_univ ~lcnt state (as_int ~lcnt b))) }, None)
  | None, None, Some (`List [ a; b ]), None ->
    ({ state with univs = RRange.append state.univs (U.IMax (get_univ ~lcnt state (as_int ~lcnt a), get_univ ~lcnt state (as_int ~lcnt b))) }, None)
  | None, None, None, Some (`Int n) ->
    ({ state with univs = RRange.append state.univs (U.UNamed (get_name ~lcnt state n)) }, None)
  | _ -> err ~lcnt "bad level record"
```

- [ ] **Step 3: Implement expression records**

Add this function after `parse_level`:

```ocaml
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
    | None, Some (`Int u), None, None, None, None, None, None, None, None, None -> Sort (get_univ ~lcnt state u)
    | None, None, Some payload, None, None, None, None, None, None, None, None ->
      let name = get_name ~lcnt state (require_int ~lcnt "name" payload) in
      let us = require_list ~lcnt "us" payload |> List.map (fun u -> get_univ ~lcnt state (as_int ~lcnt u)) in
      Const (name, us)
    | None, None, None, Some payload, None, None, None, None, None, None, None ->
      App (get_expr ~lcnt state (require_int ~lcnt "fn" payload), get_expr ~lcnt state (require_int ~lcnt "arg" payload))
    | None, None, None, None, Some payload, None, None, None, None, None, None ->
      Lam
        ( binders (require_string ~lcnt "binderInfo" payload),
          get_name ~lcnt state (require_int ~lcnt "name" payload),
          get_expr ~lcnt state (require_int ~lcnt "type" payload),
          get_expr ~lcnt state (require_int ~lcnt "body" payload) )
    | None, None, None, None, None, Some payload, None, None, None, None, None ->
      Pi
        ( binders (require_string ~lcnt "binderInfo" payload),
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
    | None, None, None, None, None, None, None, None, Some (`String n), None, None -> Nat (Z.of_string n)
    | None, None, None, None, None, None, None, None, None, Some (`String s), None -> String s
    | None, None, None, None, None, None, None, None, None, None, Some payload ->
      get_expr ~lcnt state (require_int ~lcnt "expr" payload)
    | _ -> err ~lcnt "bad expression record"
  in
  ({ state with exprs = RRange.append state.exprs expr }, None)
```

- [ ] **Step 4: Implement axiom, def, theorem, opaque, and quot records**

Add these functions after `parse_expr`:

```ocaml
let level_params ~lcnt state payload =
  require_list ~lcnt "levelParams" payload |> List.map (fun n -> get_name ~lcnt state (as_int ~lcnt n))

let parse_axiom ~lcnt state payload =
  let name = get_name ~lcnt state (require_int ~lcnt "name" payload) in
  Feedback.msg_info Pp.(str "line " ++ int lcnt ++ str ": " ++ N.pp name);
  let ty = get_expr ~lcnt state (require_int ~lcnt "type" payload) in
  let univs = level_params ~lcnt state payload in
  (state, Some (Entry (Ax { name; ty; univs })))

let parse_deflike ~lcnt state payload =
  let name = get_name ~lcnt state (require_int ~lcnt "name" payload) in
  Feedback.msg_info Pp.(str "line " ++ int lcnt ++ str ": " ++ N.pp name);
  let ty = get_expr ~lcnt state (require_int ~lcnt "type" payload) in
  let body = get_expr ~lcnt state (require_int ~lcnt "value" payload) in
  let univs = level_params ~lcnt state payload in
  (state, Some (Entry (Def { name; ty; body; univs })))

let parse_quot ~lcnt state payload =
  ignore (require_string ~lcnt "kind" payload);
  Feedback.msg_info Pp.(str "line " ++ int lcnt ++ str ": " ++ N.pp LeanParse.quot_name);
  (state, Some (Entry (Quot LeanParse.quot_name)))
```

- [ ] **Step 5: Dispatch supported records from `do_line`**

Replace the final unsupported-record branch in `do_line` with:

```ocaml
    | None ->
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
          member "quot" json )
      with
      | Some _, None, None, None, None, None, None, None, None, None, None, None
      | None, Some _, None, None, None, None, None, None, None, None, None, None -> parse_name ~lcnt state json
      | None, None, Some _, None, None, None, None, None, None, None, None, None
      | None, None, None, Some _, None, None, None, None, None, None, None, None
      | None, None, None, None, Some _, None, None, None, None, None, None, None
      | None, None, None, None, None, Some _, None, None, None, None, None, None -> parse_level ~lcnt state json
      | None, None, None, None, None, None, Some _, None, None, None, None, None -> parse_expr ~lcnt state json
      | None, None, None, None, None, None, None, Some payload, None, None, None, None -> parse_axiom ~lcnt state payload
      | None, None, None, None, None, None, None, None, Some payload, None, None, None -> parse_deflike ~lcnt state payload
      | None, None, None, None, None, None, None, None, None, Some payload, None, None -> parse_deflike ~lcnt state payload
      | None, None, None, None, None, None, None, None, None, None, Some payload, None -> parse_deflike ~lcnt state payload
      | None, None, None, None, None, None, None, None, None, None, None, Some payload -> parse_quot ~lcnt state payload
      | _ -> err ~lcnt "unsupported NDJSON record"
```

- [ ] **Step 6: Run the build**

Run:

```bash
make
```

Expected: PASS.

- [ ] **Step 7: Commit basic record parsing**

```bash
git add src/leanParseNdjson.ml
git commit -m "feat: parse basic lean4export ndjson records"
```

## Task 5: Implement NDJSON Inductive Group Parsing

**Files:**
- Modify: `src/leanParseNdjson.ml`
- Test: `make`

- [ ] **Step 1: Add inductive value decoders**

Add these helpers after `parse_quot`:

```ocaml
let parse_ctor_val ~lcnt state ctor_json =
  let name = get_name ~lcnt state (require_int ~lcnt "name" ctor_json) in
  let ty = get_expr ~lcnt state (require_int ~lcnt "type" ctor_json) in
  (name, ty)

let parse_ind_val ~lcnt state ind_json ctor_jsons =
  let name = get_name ~lcnt state (require_int ~lcnt "name" ind_json) in
  Feedback.msg_info Pp.(str "line " ++ int lcnt ++ str ": " ++ N.pp name);
  let nparams = require_int ~lcnt "numParams" ind_json in
  let ty0 = get_expr ~lcnt state (require_int ~lcnt "type" ind_json) in
  let params, ty = LeanParse.pop_params nparams ty0 in
  let ctors =
    ctor_jsons
    |> List.map (parse_ctor_val ~lcnt state)
    |> List.map (fun (ctor_name, ctor_ty) -> (ctor_name, LeanParse.fix_ctor name nparams ctor_ty))
  in
  let univs = level_params ~lcnt state ind_json in
  Entry (Ind { name; params; ty; ctors; univs })

let parse_inductive ~lcnt state payload =
  let types = require_list ~lcnt "types" payload in
  let ctors = require_list ~lcnt "ctors" payload in
  match types with
  | [ ind_json ] -> (state, Some (parse_ind_val ~lcnt state ind_json ctors))
  | _ -> err ~lcnt "mutual inductive groups are not supported by the current importer model"
```

- [ ] **Step 2: Dispatch inductive records**

Extend the record dispatch tuple in `do_line` with `member "inductive" json`, and add this case:

```ocaml
| None, None, None, None, None, None, None, None, None, None, None, None, Some payload ->
  parse_inductive ~lcnt state payload
```

Keep the existing catch-all case:

```ocaml
| _ -> err ~lcnt "unsupported NDJSON record"
```

- [ ] **Step 3: Run the build**

Run:

```bash
make
```

Expected: PASS, or a compile error only from the dispatch tuple arity. If there is a tuple arity error, update every pattern in the dispatch match to include the new final `inductive` slot.

- [ ] **Step 4: Commit inductive parsing**

```bash
git add src/leanParseNdjson.ml
git commit -m "feat: parse lean4export inductive records"
```

## Task 6: Dispatch `Lean Import` By Dump Format

**Files:**
- Modify: `src/lean.ml`
- Test: `make`

- [ ] **Step 1: Replace the input state with format-aware parser state**

In `src/lean.ml`, replace:

```ocaml
type input_state = {
  pstate : LeanParse.parsing_state;
  skips : int;
}
```

with:

```ocaml
type parser_state =
  | OldParser of LeanParse.parsing_state
  | NdjsonParser of LeanParseNdjson.parsing_state

type input_state = {
  pstate : parser_state;
  skips : int;
}
```

- [ ] **Step 2: Add parser-state pretty-printing**

Add near `finish`:

```ocaml
let pp_parser_state = function
  | OldParser pstate -> LeanParse.pp_state pstate
  | NdjsonParser pstate -> LeanParseNdjson.pp_state pstate
```

In `finish`, replace:

```ocaml
LeanParse.pp_state state.pstate ++
```

with:

```ocaml
pp_parser_state state.pstate ++
```

- [ ] **Step 3: Route line parsing through the selected parser**

Replace the `do_line` wrapper that currently calls `LeanParse.do_line` with:

```ocaml
let do_line state l =
  let do_line () =
    match state.pstate with
    | OldParser pstate ->
      let pstate, action = LeanParse.do_line pstate ~lcnt:!lcnt l in
      ({ state with pstate = OldParser pstate }, action)
    | NdjsonParser pstate ->
      let pstate, action = LeanParseNdjson.do_line pstate ~lcnt:!lcnt l in
      ({ state with pstate = NdjsonParser pstate }, action)
  in
  match !timeout with
  | None -> do_line ()
  | Some t ->
    (match Control.timeout (float_of_int t) do_line () with
    | Ok v -> v
    | Error info -> Exninfo.iraise (TimedOut, info))
```

Update the timing wrapper below it so it still calls `do_line state l`.

- [ ] **Step 4: Update `do_input` to use the full updated state**

In `do_input`, replace:

```ocaml
let pstate, oentry = do_line state.pstate l in
let state = { state with pstate } in
```

with:

```ocaml
let state, oentry = do_line state l in
```

Also preserve ranged-import behavior in the earlier `before_from` branch:
old-format dumps may still skip prefix lines without parsing because their parser
state is persisted through summaries, but NDJSON dumps must parse skipped prefix
lines with a prefix-only parser path and ignore declaration/action records. This
rebuilds the metadata, name, level, and expression tables before the first
imported line while still avoiding `add_entry` and avoiding declaration
validation for lines before `from`.

- [ ] **Step 5: Add format detection when opening the file**

Format detection must scan to the first non-empty physical line before deciding
which parser to use. Blank lines before NDJSON metadata must not cause fallback
to the old parser.

Replace the body of `import` with:

```ocaml
let import ~from ~until f =
  lcnt := 1;
  let rec first_non_empty_line ch =
    match input_line ch with
    | l ->
      if String.trim l = "" then first_non_empty_line ch
      else Some l
    | exception End_of_file -> None
  in
  let ch = open_in f in
  let first_line = first_non_empty_line ch in
  close_in ch;
  let initial_parser =
    match first_line with
    | Some l when LeanParseNdjson.is_ndjson_line l -> NdjsonParser LeanParseNdjson.empty_state
    | _ -> OldParser !pstate
  in
  let { pstate = pstatev } =
    Flags.silently
      (fun () -> do_input { pstate = initial_parser; skips = 0 } ~from ~until (open_in f))
      ()
  in
  let old_pstate =
    match pstatev with
    | OldParser pstate -> pstate
    | NdjsonParser _ -> !pstate
  in
  pstate := old_pstate;
  Lib.add_leaf (lean_obj (old_pstate, !sets, !declared, !entries, !squash_info, !height_cache))
```

This preserves old parser summary state in Rocq summaries. NDJSON parser state is not reused across imports in this milestone.

- [ ] **Step 6: Run the build**

Run:

```bash
make
```

Expected: PASS.

- [ ] **Step 7: Commit import dispatch**

```bash
git add src/lean.ml
git commit -m "feat: dispatch lean import by dump format"
```

## Task 7: Add Rocq Smoke Test For Minimal NDJSON Import

**Files:**
- Create: `tests/ndjson_smoke.v`
- Modify: `tests/_CoqProject`
- Test: `make test`

- [ ] **Step 1: Create the smoke test**

Create `tests/ndjson_smoke.v`:

```coq
From LeanImport Require Import Lean.

Set Lean Just Parsing.
Redirect "ndjson_smoke.log" Lean Import "fixtures/ndjson/minimal.ndjson".
Unset Lean Just Parsing.
```

- [ ] **Step 2: Add the test file to the test project**

Append this line to `tests/_CoqProject`:

```text
ndjson_smoke.v
```

- [ ] **Step 3: Run the test target**

Run:

```bash
make test
```

Expected: PASS. If unrelated legacy fixture tests fail, run the focused generated command from `tests/Makefile.rocq` for `ndjson_smoke.v` and record the unrelated failure in the commit message body.

- [ ] **Step 4: Commit the smoke test**

```bash
git add tests/ndjson_smoke.v tests/_CoqProject
git commit -m "test: import minimal lean4export ndjson dump"
```

## Task 8: Add Fixture Manifest And Local Lean Sources

**Files:**
- Create: `lean/fixtures/manifest.toml`
- Create: `lean/fixtures/Ulift.lean`
- Create: `lean/fixtures/Pnni.lean`
- Create: `lean/fixtures/AnomalyPrintProjections.lean`
- Create: `lean/fixtures/BinTree.lean`
- Create: `lean/fixtures/List.lean`
- Create: `lean/fixtures/Logic.lean`
- Create: `lean/fixtures/Quot.lean`
- Test: `git diff --check`

- [ ] **Step 1: Create the manifest**

Create `lean/fixtures/manifest.toml`:

```toml
[toolchain]
lean4export_repository = "https://github.com/leanprover/lean4export"
# Documentation ref only; regeneration checks out lean4export_commit.
lean4export_ref = "master"
lean4export_commit = "12581a6b680d8478175596338eb2d53383a323e3"
lean_toolchain = "leanprover/lean4:v4.30.0-rc2"
export_format = "3.1.0"

[[dump]]
name = "core"
output = "dumps/core.ndjson"
kind = "upstream_module"
module = "Init.Core"
default = true

[[dump]]
name = "init"
output = "dumps/init.ndjson"
kind = "upstream_module"
module = "Init"
default = true

[[dump]]
name = "stdlib"
output = "dumps/stdlib.ndjson"
kind = "upstream_module"
module = "Std"
default = false
expensive = true

[[dump]]
name = "ulift"
output = "dumps/ulift.ndjson"
kind = "local_module"
module = "Ulift"
default = true

[[dump]]
name = "pnni"
output = "dumps/pnni.ndjson"
kind = "local_module"
module = "Pnni"
default = true

[[dump]]
name = "anomaly_print_projections"
output = "dumps/anomaly_print_projections.ndjson"
kind = "local_module"
module = "AnomalyPrintProjections"
default = true

[[dump]]
name = "bin_tree"
output = "dumps/bin_tree.ndjson"
kind = "local_module"
module = "BinTree"
default = true

[[dump]]
name = "list"
output = "dumps/list.ndjson"
kind = "local_module"
module = "List"
default = true

[[dump]]
name = "logic"
output = "dumps/logic.ndjson"
kind = "local_module"
module = "Logic"
default = true

[[dump]]
name = "quot"
output = "dumps/quot.ndjson"
kind = "local_module"
module = "Quot"
default = true
```

- [ ] **Step 2: Create local fixture source files**

Create `lean/fixtures/Ulift.lean`:

```lean
namespace Scratch

inductive MyNat : Type where
  | zero : MyNat

inductive MyProd (α : Sort u) (β : Sort v) : Sort (max u v) where
  | mk : α -> β -> MyProd α β

def example1 : MyProd (ULift.{1, 0} MyNat) Type :=
  MyProd.mk (ULift.up MyNat.zero) Type

def useUp.{u} (α : Type u) (x : α) : ULift.{u, u} α :=
  ULift.up x

end Scratch
```

Create `lean/fixtures/Pnni.lean`:

```lean
namespace Scratch

axiom plus_n_n_injective (n m : Nat) : n + n = m + m -> n = m

end Scratch
```

Create `lean/fixtures/AnomalyPrintProjections.lean`:

```lean
namespace Scratch

inductive aexp where
  | num : Nat -> aexp
  | plus : aexp -> aexp -> aexp

def aeval : aexp -> Nat
  | aexp.num n => n
  | aexp.plus a b => aeval a + aeval b

end Scratch
```

Create `lean/fixtures/BinTree.lean`:

```lean
namespace Scratch

inductive BinTree (α : Type u) where
  | leaf : α -> BinTree α
  | node : BinTree α -> BinTree α -> BinTree α

end Scratch
```

Create `lean/fixtures/List.lean`:

```lean
namespace Scratch

def listId (xs : List Nat) : List Nat := xs

end Scratch
```

Create `lean/fixtures/Logic.lean`:

```lean
namespace Scratch

theorem and_comm (p q : Prop) : p ∧ q -> q ∧ p := by
  intro h
  exact And.intro h.right h.left

end Scratch
```

Create `lean/fixtures/Quot.lean`:

```lean
namespace Scratch

def quotExample : Quot (fun (a b : Nat) => a = b) :=
  Quot.mk _ 0

end Scratch
```

- [ ] **Step 3: Check formatting of added files**

Run:

```bash
git diff --check
```

Expected: PASS.

- [ ] **Step 4: Commit manifest and local sources**

```bash
git add lean/fixtures/manifest.toml lean/fixtures/*.lean
git commit -m "testdata: add lean fixture regeneration sources"
```

## Task 9: Add Regeneration Script And Make Target

**Files:**
- Create: `scripts/regenerate-dumps.sh`
- Create: `lean/fixtures/lean-toolchain`
- Create: `lean/fixtures/lakefile.lean`
- Modify: `Makefile`
- Modify: `lean/fixtures/manifest.toml`
- Test: `scripts/regenerate-dumps.sh --help`

Reliability requirements:
- `lean/fixtures/manifest.toml` pins `lean4export_commit`; `lean4export_ref` is documentation only.
- The script checks out the pinned commit instead of a moving branch head.
- Requested dump names are validated against the manifest before Lean tooling is required. Unknown names fail with `error: unknown dump requested: <name>`, and selecting zero dumps is an error.
- Exports are written to a temporary file in the target output directory, validated there, and atomically moved into place only after validation succeeds. Temporary files are removed on failure so a failed export does not truncate an existing dump.

- [ ] **Step 1: Create the regeneration script**

Create `scripts/regenerate-dumps.sh`:

```bash
#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
MANIFEST="$ROOT/lean/fixtures/manifest.toml"
CACHE="${LEAN4EXPORT_CACHE:-$ROOT/.cache/lean4export}"
REF="master"
TOOLCHAIN="leanprover/lean4:v4.30.0-rc2"

usage() {
  cat <<'USAGE'
Usage: scripts/regenerate-dumps.sh [--all] [dump-name]

Regenerates maintained NDJSON dumps with lean4export.
Default mode regenerates manifest entries marked default=true.
--all includes expensive optional entries.
USAGE
}

if [[ "${1:-}" == "--help" ]]; then
  usage
  exit 0
fi

for tool in git lake lean elan; do
  if ! command -v "$tool" >/dev/null 2>&1; then
    echo "error: missing required tool: $tool" >&2
    exit 1
  fi
done

mkdir -p "$(dirname "$CACHE")"
if [[ ! -d "$CACHE/.git" ]]; then
  git clone https://github.com/leanprover/lean4export "$CACHE"
fi

git -C "$CACHE" fetch origin "$REF"
git -C "$CACHE" checkout FETCH_HEAD

ACTUAL_TOOLCHAIN="$(tr -d '\r\n' < "$CACHE/lean-toolchain")"
if [[ "$ACTUAL_TOOLCHAIN" != "$TOOLCHAIN" ]]; then
  echo "error: lean4export toolchain mismatch: expected $TOOLCHAIN, got $ACTUAL_TOOLCHAIN" >&2
  exit 1
fi

(cd "$CACHE" && lake build)

ALL=false
if [[ "${1:-}" == "--all" ]]; then
  ALL=true
  shift
fi

requested=("$@")

emit_entries() {
  awk '
    /^\[\[dump\]\]/ {
      if (name != "") print name "|" output "|" kind "|" module "|" default
      name=output=kind=module=default=""
      next
    }
    /^name = / { gsub(/"/, "", $3); name=$3; next }
    /^output = / { gsub(/"/, "", $3); output=$3; next }
    /^kind = / { gsub(/"/, "", $3); kind=$3; next }
    /^module = / { gsub(/"/, "", $3); module=$3; next }
    /^default = / { default=$3; next }
    END { if (name != "") print name "|" output "|" kind "|" module "|" default }
  ' "$MANIFEST"
}

selected() {
  local name="$1"
  local default="$2"
  if (( ${#requested[@]} > 0 )); then
    for req in "${requested[@]}"; do
      [[ "$req" == "$name" ]] && return 0
    done
    return 1
  fi
  [[ "$ALL" == true || "$default" == true ]]
}

LOCAL_LAKE="$ROOT/lean/fixtures/lakefile.lean"
if [[ ! -f "$LOCAL_LAKE" ]]; then
  echo "error: missing local fixture Lake file: $LOCAL_LAKE" >&2
  exit 1
fi

while IFS='|' read -r name output kind module default; do
  if ! selected "$name" "$default"; then
    continue
  fi
  out="$ROOT/$output"
  mkdir -p "$(dirname "$out")"
  case "$kind" in
    upstream_module)
      (cd "$CACHE" && lake env .lake/build/bin/lean4export "$module") > "$out"
      ;;
    local_module)
      (cd "$ROOT/lean/fixtures" && lake env "$CACHE/.lake/build/bin/lean4export" "$module") > "$out"
      ;;
    *)
      echo "error: unsupported dump kind for $name: $kind" >&2
      exit 1
      ;;
  esac
  if [[ ! -s "$out" ]]; then
    echo "error: generated dump is empty: $output" >&2
    exit 1
  fi
  if ! head -n 1 "$out" | grep -q '"meta"'; then
    echo "error: generated dump lacks NDJSON metadata: $output" >&2
    exit 1
  fi
  echo "generated $output"
done < <(emit_entries)
```

- [ ] **Step 2: Add fixture Lake files**

Create `lean/fixtures/lean-toolchain`:

```text
leanprover/lean4:v4.30.0-rc2
```

Create `lean/fixtures/lakefile.lean`:

```lean
import Lake
open Lake DSL

package fixtures

lean_lib Ulift
lean_lib Pnni
lean_lib AnomalyPrintProjections
lean_lib BinTree
lean_lib List
lean_lib Logic
lean_lib Quot
```

- [ ] **Step 3: Make the script executable**

Run:

```bash
chmod +x scripts/regenerate-dumps.sh
```

- [ ] **Step 4: Add the Make target**

Add this target after the existing `submake` target in `Makefile`, preserving `submake` as the first non-special target so plain `make` continues to run the default Rocq build:

```make
.PHONY: regenerate-dumps
regenerate-dumps:
	./scripts/regenerate-dumps.sh
```

- [ ] **Step 5: Test help output**

Run:

```bash
scripts/regenerate-dumps.sh --help
```

Expected: usage output succeeds without requiring Lean tooling.

- [ ] **Step 6: Run a local fixture regeneration when Lean tooling is installed**

Run:

```bash
scripts/regenerate-dumps.sh ulift
```

Expected: `dumps/ulift.ndjson` is generated and starts with a `meta` JSON object. If Lean tooling is not available in the environment, record the exact missing-tool error and do not include a regenerated dump.

- [ ] **Step 7: Commit manifest regeneration**

```bash
git add Makefile scripts/regenerate-dumps.sh lean/fixtures/lean-toolchain lean/fixtures/lakefile.lean lean/fixtures/manifest.toml
git commit -m "tooling: regenerate dumps from fixture manifest"
```

## Task 10: Update Documentation

**Files:**
- Modify: `README.md`
- Test: `rg -n "NDJSON|regenerate-dumps|lean4export" README.md`

- [ ] **Step 1: Update the Lean 4 usage section**

In `README.md`, replace the Lean 4 paragraph under the usage section with:

```markdown
For use with Lean 4, use [lean4export](https://github.com/leanprover/lean4export).
Current maintained fixtures target the Lean toolchain pinned by `lean4export`
master and the Lean 4 NDJSON export format `3.1.0`.
```

- [ ] **Step 2: Add a regeneration section**

Add this section after the example dump list:

````markdown
## Regenerating Lean 4 dumps

Maintained Lean 4 fixtures are described in `lean/fixtures/manifest.toml`.
Upstream-backed fixtures name Lean modules from the toolchain pinned by
`lean4export`; local regression fixtures live under `lean/fixtures/`.

To regenerate the default fixture set:

```sh
make regenerate-dumps
```

To regenerate a specific fixture:

```sh
scripts/regenerate-dumps.sh ulift
```

The script requires `elan`, `lean`, `lake`, and `git`. It builds
`lean4export`, verifies the pinned `lean-toolchain`, exports the selected
modules, and checks that generated dumps start with NDJSON metadata.
````

- [ ] **Step 3: Verify documentation references**

Run:

```bash
rg -n "NDJSON|regenerate-dumps|lean4export" README.md
```

Expected: output includes the new Lean 4 usage paragraph and regeneration section.

- [ ] **Step 4: Commit documentation**

```bash
git add README.md
git commit -m "docs: document lean4export ndjson regeneration"
```

## Task 11: Final Verification And Cleanup

**Files:**
- Inspect: all modified files
- Test: `make`
- Test: `make test`
- Test: `git status --short`

- [ ] **Step 1: Run full build**

Run:

```bash
make
```

Expected: PASS.

- [ ] **Step 2: Run full tests**

Run:

```bash
make test
```

Expected: PASS, or documented legacy fixture failures unrelated to NDJSON parser integration.

- [ ] **Step 3: Verify regeneration script help**

Run:

```bash
scripts/regenerate-dumps.sh --help
```

Expected: usage output succeeds.

- [ ] **Step 4: Verify working tree**

Run:

```bash
git status --short
```

Expected: clean working tree except for user-owned untracked `.codex` if still present.

- [ ] **Step 5: Record verification in the final handoff**

Include:

```text
Verified:
- make
- make test
- scripts/regenerate-dumps.sh --help
```

If a command could not run because Lean tooling is missing, include the exact missing-tool message.
