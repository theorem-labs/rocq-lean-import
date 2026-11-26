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

(* Two Fin values that differ at a place the kernel converts on its own give no lemma, and the other places of
   the same argument are still cast. dumps/lean434/fin_values.ndjson is exported from
   dumps/lean434/src/RLI434Values.lean: RLI434V.values_differ (export line 8086) :
   f c3 /\ 2500 + 2500 = 5000 -> f c4 /\ 5000 = 5000 := fun h => h, with f := fun _ : UInt8 => True and the
   UInt8 values c3 := 3 and c4 := 4. The Fin pair c3, c4 has the values 3 and 4: no lemma, and the kernel
   converts f c3 with f c4 by unfolding f; the Nat pair 2500 + 2500, 5000 beside it is cast along
   RLI434V_values_differ__nat_eq_1. *)
Redirect "fin_transport_values_differ.log" Lean Import "../dumps/lean434/fin_values.ndjson".

Check RLI434V_values_differ.
Check RLI434V_values_differ__nat_eq_1.
