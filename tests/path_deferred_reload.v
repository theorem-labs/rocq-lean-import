From LeanImport Require Import Lean.
From Test Require path_deferred_saved.

(* V9c: the entries of tests/path_deferred_saved.v, loaded from its compiled library, keep the path and
   version of their export (Lean 4.25.0). The import of dumps/lean434/string_deferred_4260.ndjson (Lean
   4.26.0) asks for the instance of RLI425.plit at Prop, which the saved import left undeclared: it is
   declared with String.mk, and RLI426.pair's own literal with String.ofList, as in
   tests/path_deferred_string.v. tests/path_deferred_reload.expect checks the logs. *)
Set Lean Error Mode "Fail".
Redirect "path_deferred_reload.log" Lean Import "../dumps/lean434/string_deferred_4260.ndjson".

Check RLI426_pair_eq.
Redirect "path_deferred_reload_plit_inst1.log" Print RLI425_plit_inst1.
