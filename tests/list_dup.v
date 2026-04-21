From LeanImport Require Import Lean.

(* Duplicate #IND for the same name should be skipped with a warning
   (mirrors what lean4export emits when shared transitive deps are
   listed twice in export_definitions). *)
Redirect "list_dup.log" Lean Import "../dumps/list_dup".

Print list.
Print test.
Fail Print list0.
Fail Print list_nil0.
