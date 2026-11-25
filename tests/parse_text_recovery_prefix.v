From LeanImport Require Import Lean.

Set Lean Error Mode "Skip".
(* Text range imports skip the prefix and reuse the parser state saved by the
   preceding import. The first range stops just after refusing expression 3. *)
Redirect "parse_text_recovery_first.log" Lean Import "../dumps/parse_text_recovery" 1 12.
Redirect "parse_text_recovery_prefix.log" Lean Import "../dumps/parse_text_recovery" 12 16.
(* r5 log: "parse_text_recovery_prefix.log" Skipping: Error at line 12 (for line-12): 4 #EC 2 *)
(* r5 log: "parse_text_recovery_prefix.log" "File "src/leanParse.ml", line 172, characters 8-14: Assertion failed." *)
(* r5 error: The reference RLITextAfter was not found *)
Check RLITextAfter.
Fail Check RLITextRefused.
