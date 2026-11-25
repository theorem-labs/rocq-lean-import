From LeanImport Require Import Lean.

Set Lean Error Mode "Skip".
Redirect "parse_text_numbering.log" Lean Import "../dumps/parse_text_numbering".
(* r5 log lacks: "parse_text_numbering.log" Skipping: Error at line 10 (for line-10): 99 #ELN 7 *)
(* r5 log: "parse_text_numbering.log" Skipping: Error at line 21 (for line-21): 3 #ES 4 *)
(* r5 error: The reference RLITextAfterGaps was not found *)
Check RLITextAfterGaps.
