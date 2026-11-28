From LeanImport Require Import Lean.

(* W11: the Fin reader must reuse completed work. Each c(i+1) is c(i) * c(i).
   The checked cast succeeds even though following all occurrences would not. *)
Set Warnings "+unknown-option".
Set Lean Error Mode "Fail".
Set Lean Entry Timeout 20.
Redirect "fin_transport_share.log" Lean Import "../dumps/lean434/fin_share.ndjson" 1 8771.
Check RLI434Sh_share_60.
Check RLI434Sh_share_60__nat_eq_1.
