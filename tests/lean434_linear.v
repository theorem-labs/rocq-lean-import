From LeanImport Require Import Lean.

Set Lean Error Mode "Fail".
Timeout 30 Lean Import "../dumps/lean434/linear.ndjson".

Check Nat_Internal_Linear_ExprCnstr_denote_toNormPoly.
