From LeanImport Require Import Lean.

(* The test project enables Rocq's Fail notices in batch mode. *)
Set Lean Error Mode "Fail".

(* Each fixture plants one change in an export; the import must refuse the
   entry the "planted" line names. Fail drops each import's changes. The log
   checks name the refused entry. *)
(* planted: Nat.pow_succ *)
(* N1: Nat.pow_succ with a false statement (its right-hand side made n^m) and
   its original proof is refused. *)
Redirect "negative_controls_n1.log" Fail Lean Import "../dumps/lean434/negative_pow_statement.ndjson".
(* N2: Nat.pow_succ with the proof of another theorem (Nat.pow_zero) is
   refused. *)
Redirect "negative_controls_n2.log" Fail Lean Import "../dumps/lean434/negative_pow_proof.ndjson".
(* planted: Nat.le *)
(* N3_NEW: on the new path, a Nat.le whose constructor has a field of another
   type than the predeclared Nat_le's is refused. *)
Redirect "negative_controls_n3_new.log" Fail Lean Import "../dumps/lean434/negative_le_field.ndjson".
(* planted: Fin *)
(* N3_LEGACY: on the legacy path, a Fin whose constructor has a field of
   another type than the predeclared Fin's is refused. *)
Redirect "negative_controls_n3_legacy.log" Fail Lean Import "../dumps/lean434/negative_fin_field.ndjson".
(* A Fin in Type 1, one universe above Lean's Type, is refused: the
   predeclared Fin is in Set, which stands only for Lean's Type. *)
Redirect "negative_controls_fin_sort.log" Fail Lean Import "../dumps/lean434/negative_fin_sort.ndjson".
(* planted: UInt32.size *)
(* N4_LEGACY: on the legacy path, a UInt32.size whose declared type is Type,
   not Nat, is refused. *)
Redirect "negative_controls_n4_legacy.log" Fail Lean Import "../dumps/lean434/pred_uint32_size.ndjson".
(* N4_NEW: on the new path, a Nat.le in Type, where the predeclared Nat_le is
   in SProp, is refused. *)
Redirect "negative_controls_n4_new.log" Fail Lean Import "../dumps/lean434/negative_le_type.ndjson".
(* planted: Nat.pow_zero *)
(* N5: on the new path Nat.pow is imported from the export, not predeclared:
   with a body that returns zero, the rfl proof of Nat.pow_zero is refused. *)
Redirect "negative_controls_n5.log" Fail Lean Import "../dumps/lean434/negative_pow_body.ndjson".
(* planted: sizeIsFive *)
(* N6: on the legacy path the predeclared UInt32.size keeps its value 2^32:
   an export whose UInt32.size is 5 cannot prove sizeIsFive : UInt32.size = 5
   by rfl. *)
Redirect "negative_controls_n6.log" Fail Timeout 20 Lean Import "../dumps/lean434/negative_size_body.ndjson".

(* In Skip mode the refused Nat.pow_succ is not declared. *)
Set Lean Error Mode "Skip".
Redirect "negative_controls_absent.log" Timeout 20 Lean Import "../dumps/lean434/negative_pow_statement.ndjson".
Fail Check Nat_pow_succ.
