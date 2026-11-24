From LeanImport Require Import Lean.

(* The test project enables Rocq's Fail notices in batch mode. *)
Set Lean Error Mode "Fail".

(* Fail drops each import's changes. The log checks name the refused entry. *)
(* planted: Nat.pow_succ *)
(* N1 *)
Redirect "negative_controls_n1.log" Fail Lean Import "../dumps/lean434/negative_pow_statement.ndjson".
(* N2 *)
Redirect "negative_controls_n2.log" Fail Lean Import "../dumps/lean434/negative_pow_proof.ndjson".
(* planted: Nat.le *)
(* N3_NEW *)
Redirect "negative_controls_n3_new.log" Fail Lean Import "../dumps/lean434/negative_le_field.ndjson".
(* planted: Fin *)
(* N3_LEGACY *)
Redirect "negative_controls_n3_legacy.log" Fail Lean Import "../dumps/lean434/negative_fin_field.ndjson".
(* planted: UInt32.size *)
(* N4_LEGACY *)
Redirect "negative_controls_n4_legacy.log" Fail Lean Import "../dumps/lean434/pred_uint32_size.ndjson".
(* N4_NEW *)
Redirect "negative_controls_n4_new.log" Fail Lean Import "../dumps/lean434/negative_le_type.ndjson".
(* planted: Nat.pow_zero *)
(* N5 *)
Redirect "negative_controls_n5.log" Fail Lean Import "../dumps/lean434/negative_pow_body.ndjson".
(* planted: sizeIsFive *)
(* N6 *)
Redirect "negative_controls_n6.log" Fail Timeout 20 Lean Import "../dumps/lean434/negative_size_body.ndjson".

Set Lean Error Mode "Skip".
Redirect "negative_controls_absent.log" Timeout 20 Lean Import "../dumps/lean434/negative_pow_statement.ndjson".
Fail Check Nat_pow_succ.
