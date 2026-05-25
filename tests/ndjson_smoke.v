From LeanImport Require Import Lean.

Set Lean Just Parsing.
Redirect "ndjson_smoke.log" Lean Import "fixtures/ndjson/minimal.ndjson".
Unset Lean Just Parsing.
