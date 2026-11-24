From LeanImport Require Import Lean.

Set Lean Error Mode "Fail".

(* Succeed discards a case's declarations before the next case. *)
Redirect "path_choice_old.log" Succeed Lean Import "../dumps/lean434/path_old.txt".
Redirect "path_choice_4169.log" Succeed Lean Import "../dumps/lean434/path_4169.ndjson".
Redirect "path_choice_3.log" Succeed Lean Import "../dumps/lean434/path_3.ndjson".
Redirect "path_choice_4170.log" Succeed Lean Import "../dumps/lean434/path_4170.ndjson".
Redirect "path_choice_4180.log" Succeed Lean Import "../dumps/lean434/path_4180.ndjson".
Redirect "path_choice_4300.log" Succeed Lean Import "../dumps/lean434/path_4300.ndjson".
Redirect "path_choice_500.log" Succeed Lean Import "../dumps/lean434/path_500.ndjson".
Redirect "path_choice_rc.log" Succeed Lean Import "../dumps/lean434/path_rc.ndjson".
Redirect "path_choice_nightly.log" Succeed Lean Import "../dumps/lean434/path_nightly.ndjson".
Redirect "path_choice_v.log" Succeed Lean Import "../dumps/lean434/path_v.ndjson".
Redirect "path_choice_no_lean.log" Succeed Lean Import "../dumps/lean434/path_no_lean.ndjson".
Redirect "path_choice_no_version.log" Succeed Lean Import "../dumps/lean434/path_no_version.ndjson".
Redirect "path_choice_empty_version.log" Succeed Lean Import "../dumps/lean434/path_empty_version.ndjson".
Redirect "path_choice_numeric.log" Succeed Lean Import "../dumps/lean434/path_numeric.ndjson".
Redirect "path_choice_bad_version.log" Succeed Lean Import "../dumps/lean434/path_bad_version.ndjson".
Redirect "path_choice_4340.log" Lean Import "../dumps/lean434/bitvec_only.ndjson".

(* Locate shows the fully qualified binding, not only its short name. *)
Redirect "path_choice_binding.log" Locate BitVec.
