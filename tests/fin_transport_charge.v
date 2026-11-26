From LeanImport Require Import Lean.

(* W11: each remainder has one new dividend. Load its dependencies at the
   default, then isolate the last reader. Calibrate the argument budget on
   the integrated cut: modchain_200 must stop with miss charging and cast
   without it. Its argument needs 4,756 steps, and 4,349 without the charge
   of each miss; the budget below is one step under the first. modchain_20
   is the short fitting control. *)
Set Warnings "+unknown-option".
Set Lean Error Mode "Skip".
Set Lean Entry Timeout 20.
Redirect "fin_transport_charge_base.log" Lean Import "../dumps/lean434/fin_share.ndjson" 1 8770.
Redirect "fin_transport_charge_small.log" Lean Import "../dumps/lean434/fin_share.ndjson" 8771 9835.
Check RLI434Sh_modchain_20__nat_eq_1.

Set Lean Transport Step Budget 4755.
Redirect "fin_transport_charge.log" Lean Import "../dumps/lean434/fin_share.ndjson" 9835.
Fail Check RLI434Sh_modchain_200.
