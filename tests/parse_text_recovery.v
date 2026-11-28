From LeanImport Require Import Lean.

Set Lean Error Mode "Fail".
Redirect "parse_text_recovery_fail.log" Fail Lean Import "../dumps/parse_text_recovery".

Set Lean Error Mode "Skip".
Redirect "parse_text_recovery.log" Lean Import "../dumps/parse_text_recovery".
(* r5 log: "parse_text_recovery.log" Skipping: Error at line 12 (for line-12): 4 #EC 2 *)
(* r5 log: "parse_text_recovery.log" "File "src/leanParse.ml", line 172, characters 8-14: Assertion failed." *)
(* r5 error: The reference RLITextAfter was not found *)
Check RLITextAfter.
Fail Check RLITextRefused.
