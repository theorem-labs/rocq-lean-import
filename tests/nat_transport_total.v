From LeanImport Require Import Lean.

(* The step budget of the transport pass for an entry as a whole (README, "Lean Transport Step Budget"): each part
   of an entry (its own scans and walks, and each argument the pass looks at) has N steps, and all its parts
   together 10 N. dumps/lean434/nat_budget_total.ndjson is dumps/lean434/nat_budget.ndjson up to RLI434D1.refl with,
   for each of three rows R, a function RLI434D1.take_R of a Nat and 14 proofs of c11 = y_j (c11 is 8 ^ 4 = 4096,
   each y_j a sum of two literals that no other place of the file has) and an entry
     RLI434D1.R : Nat := RLI434D1.take_R t (Eq.refl c11) ... (Eq.refl c11)
  (export lines 1145, 1266 and 1389). The pass gives each argument a lemma c11 = y_j, at 41,000 to 49,000 steps an
  argument, and each entry's own part takes about 58,400 steps. N below (71,223) is the least N at which at fits
  (its 712,228 steps in all over ten): every part of these three entries stays below N, and in all under needs
  665,314 steps and at 712,228 (10 N - 2), while over needs more than 10 N (730,458): the pass transports the
  arguments of under and at, and stops at over, whose own value the kernel then accepts. The functions take_R are
  one part each, their own walk, of 58,441 to 58,780 steps (each walks its fourteen literals near 4096, each a
  chain of Nat_succ, once): the lines before under are imported at take_under's part - 1
  (58,440), so that the pass stops at take_under, and its value, which has nothing to transport, is Lean's as
  before. An importer without the option fails at the first Set below. tests/nat_transport_total.expect checks
  the logs. *)
Set Warnings "+unknown-option".
Set Lean Transport Step Budget 58440.
Set Lean Error Mode "Skip".
Set Lean Entry Timeout 60.
Redirect "nat_transport_total_take.log" Lean Import "../dumps/lean434/nat_budget_total.ndjson" 1 1145.
Set Lean Transport Step Budget 71223.
Redirect "nat_transport_total.log" Lean Import "../dumps/lean434/nat_budget_total.ndjson" 1145.

Check RLI434D1_under__nat_eq_14.
Check RLI434D1_at__nat_eq_14.
Check RLI434D1_over.
(* The lemmas the pass declared for over before it stopped stay declared (README, "Transport of proof arguments
   across Nat literals"); over's value is Lean's. *)
Check RLI434D1_over__nat_eq_1.
