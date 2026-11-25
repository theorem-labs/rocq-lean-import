From LeanImport Require Import Lean.
From Test Require path_deferred_saved.

(* V9c: the entries of tests/path_deferred_saved.v, loaded from its compiled library, keep the path and
   version of their export (Lean 4.25.0). The import of dumps/lean434/string_deferred_4260.ndjson (Lean
   4.26.0) asks for the instance of RLI425.plit at Prop, which the saved import left undeclared: it is
   declared with String.mk, and RLI426.pair's own literal with String.ofList, as in
   tests/path_deferred_string.v. tests/path_deferred_reload.expect checks the logs. *)
Set Lean Error Mode "Fail".
(* Before its fix (ci/build-9.2-cut.sh --revert-fix), the instance of RLI425.plit that this import asks for gets
   the 4.26.0 constructor, and the kernel refuses RLI426.pair_eq, whose statement holds the String_mk of the
   loaded library, qualified by its name: *)
(* r5 error: RLI426_pair = path_deferred_saved.List_cons_inst1 path_deferred_saved.String (path_deferred_saved.String_mk *)
Redirect "path_deferred_reload.log" Lean Import "../dumps/lean434/string_deferred_4260.ndjson".

Check RLI426_pair_eq.
Redirect "path_deferred_reload_plit_inst1.log" Print RLI425_plit_inst1.
