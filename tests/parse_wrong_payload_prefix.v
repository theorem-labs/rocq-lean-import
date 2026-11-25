From LeanImport Require Import Lean.

Set Lean Error Mode "Skip".
(* The wrong-kind records and their numbered dependents are all in the prefix. *)
Redirect "parse_wrong_payload_prefix.log" Lean Import "../dumps/lean434/parse_wrong_payload.ndjson" 150.
(* r5 log: "parse_wrong_payload_prefix.log" NDJSON parse error at line 133: expression id 91 is not the next expected id 90 *)
(* r5 error: The reference RLIAfter was not found *)
Check RLIAfter.
Check RLIAfterName.
Check RLIAfterUnclear.
