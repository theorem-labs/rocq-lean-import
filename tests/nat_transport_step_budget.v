From LeanImport Require Import Lean.

(* The step budget of the transport pass (README, "Lean Transport Step Budget"): N steps for each part of an
   entry (its own scans and walks, and each argument the pass looks at), and 10 N for all its parts together.
   An importer without the option fails at the Set below. *)
Set Warnings "+unknown-option".
Set Lean Transport Step Budget 1000000.

(* The budget must be a positive number of steps: 0 and -1 are refused. *)
Redirect "nat_transport_step_budget_zero.log" Fail Set Lean Transport Step Budget 0.
Redirect "nat_transport_step_budget_negative.log" Fail Set Lean Transport Step Budget -1.

(* Unset, the default (1,000,000) applies. *)
Unset Lean Transport Step Budget.
Redirect "nat_transport_step_budget_unset.log" Test Lean Transport Step Budget.
