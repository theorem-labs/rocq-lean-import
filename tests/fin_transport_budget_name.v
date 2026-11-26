From LeanImport Require Import Lean.

(* The step count of the transport pass does not depend on the name of the file that runs the import (README,
   "Lean Transport Step Budget"). This file runs two of the budget runs of tests/fin_transport_bitwise.v, of
   bud_and (dumps/lean434/bitwise.ndjson line 17928), after the same imports and at the same budgets: at the
   entry's largest part minus 1 the pass stops, at the part it casts. The memos of the pass once chose their
   slots by a hash that read the module path of each constant, which is the library of the importing file
   (Test.fin_transport_bitwise there, Test.fin_transport_budget_name here), and the universe levels the
   importer creates; with it, a run at the part could stop in one of the two files and cast in the other.
   tests/fin_transport_budget_name.expect checks the logs. *)
Set Warnings "+unknown-option".
Set Lean Error Mode "Skip".
Set Lean Entry Timeout 10.
Redirect "fin_transport_budget_name_base.log" Lean Import "../dumps/lean434/bitwise.ndjson" 1 17917.
Redirect "fin_transport_budget_name_deps.log" Lean Import "../dumps/lean434/bitwise.ndjson" 17917 17928.
Set Lean Transport Step Budget 20769.
Redirect "fin_transport_budget_name_stop.log" Succeed Lean Import "../dumps/lean434/bitwise.ndjson" 17928 17929.
Set Lean Transport Step Budget 20770.
Redirect "fin_transport_budget_name_part.log" Succeed Lean Import "../dumps/lean434/bitwise.ndjson" 17928 17929.
Unset Lean Transport Step Budget.
