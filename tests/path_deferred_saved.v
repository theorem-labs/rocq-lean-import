From LeanImport Require Import Lean.

(* V9c, first half: this library saves the import of dumps/lean434/string_deferred_4250.ndjson (Lean
   4.25.0), whose RLI425.plit has an instance, at Prop, that the import leaves undeclared.
   tests/path_deferred_reload.v loads it in another Rocq process and declares that instance. *)
Set Lean Error Mode "Fail".
Redirect "path_deferred_saved.log" Lean Import "../dumps/lean434/string_deferred_4250.ndjson".
