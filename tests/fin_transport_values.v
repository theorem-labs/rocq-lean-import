From LeanImport Require Import Lean.

(* Two Fin values that differ give no cast (README, "Transport of proof arguments across Nat literals").
   dumps/lean434/utf8size_one_planted_2047.ndjson is dumps/lean434/utf8size_one.ndjson with the statement's literal
   (127 : UInt32) changed to (2047 : UInt32) (its row in dumps/lean434/README.md), so each branch passes a proof of
   v <= UInt32.ofNatLT 127 _ where v <= (2047 : UInt32) is expected: the statement is false, and the import must
   refuse it. tests/fin_transport_values.expect checks the log: the entry (export line 11238) is refused, and the
   pass logs nothing for it. *)
Set Warnings "+unknown-option".
Set Lean Entry Timeout 60.
Set Lean Error Mode "Skip".
Redirect "fin_transport_values.log" Lean Import "../dumps/lean434/utf8size_one_planted_2047.ndjson".

Fail Check Char_utf8Size_eq_one_iff.
