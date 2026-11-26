From LeanImport Require Import Lean.

(* Lean 4.34.0's Char.utf8Size_eq_one_iff (Init/Data/String/Decode.lean 32-34) passes, in each branch of
   Char.utf8Size.fun_cases_unfolding, a proof of v <= UInt32.ofNatLT 127 _ where v <= (127 : UInt32) is expected.
   Rocq's kernel converts the two UInt32 values on the unary Nat in about 1,100 s on the Rocq 9.2 cut. The Fin case
   of the transport pass (README, "Transport of proof arguments across Nat literals") casts each such proof along a
   lemma on the two Fin values, 127 = 127 % 2 ^ 32, which the kernel checks by eq_refl.
   dumps/lean434/utf8size_one.ndjson is exported from Char.utf8Size_eq_one_iff alone (export line 11238). The src/
   of the fix's parent refuses that entry at the 120 s limit below (ci/build-9.2-cut.sh --revert-fix).
   tests/utf8size_transport_one.expect checks the logs. *)
Set Warnings "+unknown-option".
Set Lean Entry Timeout 120.
Set Lean Error Mode "Fail".
Redirect "utf8size_transport_one.log" Lean Import "../dumps/lean434/utf8size_one.ndjson".

Check Char_utf8Size_eq_one_iff.
Check Char_utf8Size_eq_one_iff__nat_eq_1.
Check Char_utf8Size_eq_one_iff__nat_eq_2.
(* A generated lemma relies on no axiom, only on the definitional UIP of Lean's eq. *)
Redirect "utf8size_transport_one_lemma.log" Print Assumptions Char_utf8Size_eq_one_iff__nat_eq_1.
