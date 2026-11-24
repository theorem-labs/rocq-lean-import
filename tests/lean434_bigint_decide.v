From LeanImport Require Import Lean.

(* Not in tests/_CoqProject: this feature is listed, not fixed. The proofs by decide and omega of
   dumps/lean434/bigint.ndjson over Int values from 2^32 to 2^64 make Rocq's kernel compute Lean's Nat.sub
   (behind Int.decLt and Int.decLe) on unary terms, one Nat_succ at a time; Lean's kernel computes it with GMP.
   Measured on Rocq 07e45e36: about 8.6 microseconds a unit, so 2^33 units take about 20 hours. See README,
   "Natural number literals". *)
Set Lean Error Mode "Fail".
Timeout 20 Lean Import "../dumps/lean434/bigint.ndjson".

Check RLI434_boundedVal__proof_1.
Check RLI434_boundedVal_val.
Check RLI434_omega_big__proof_1_1.
Check RLI434_omega_big.
Check RLI434_window__proof_1.
Check RLI434_window.
