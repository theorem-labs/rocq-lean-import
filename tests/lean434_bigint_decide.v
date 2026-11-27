From LeanImport Require Import Lean.

(* A listed feature: the test checks that its entries are refused and that the import goes on to its end
   (tests/lean434_bigint_decide.expect). The proofs by decide and omega of dumps/lean434/bigint.ndjson over Int
   values from 2^32 to 2^64 make Rocq's kernel compute Lean's Nat.sub (behind Int.decLt and Int.decLe) on unary
   terms, one Nat_succ at a time; Lean's kernel computes it with GMP. Measured on Rocq 07e45e36: about 8.6
   microseconds a unit, so 2^33 units take about 20 hours. See README, "Natural number literals". When a change
   makes these entries import, this test fails: the feature is then fixed, and its row in
   tests/lean434_features.txt moves to fixed. RLI434.window._proof_1 (line 75984) now imports through the transport
   pass's chained waits (README, "Transport of proof arguments across Nat literals"): its argument is cast, so the
   expect file asserts the transported line. RLI434.boundedVal._proof_1 and RLI434.omega_big._proof_1_1 remain
   skipped, and the row stays listed. *)
Set Lean Error Mode "Skip".
Set Warnings "+unknown-option".
Set Lean Entry Timeout 5.
Redirect "lean434_bigint_decide.log" Lean Import "../dumps/lean434/bigint.ndjson".

Check RLI434_big_fields.
