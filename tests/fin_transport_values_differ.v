From LeanImport Require Import Lean.

(* Two Fin values that differ at a place the kernel converts on its own give no lemma, and the other places of
   the same argument are still cast (README, "Transport of proof arguments across Nat literals").
   dumps/lean434/fin_values.ndjson is exported from dumps/lean434/src/RLI434Values.lean:
   RLI434V.values_differ (export line 8086) :
     f c3 /\ 549755813888 + 549755813888 = 1099511627776 -> f c4 /\ 1099511627776 = 1099511627776 := fun h => h,
   with f := fun _ : UInt8 => True and the UInt8 values c3 := 3 and c4 := 4. The Fin pair c3, c4 has the values
   3 and 4: no lemma, and the kernel converts f c3 with f c4 by unfolding f. The Nat pair 2 ^ 39 + 2 ^ 39, 2 ^ 40
   beside it is cast along RLI434V_values_differ__nat_eq_1, which the kernel checks through Rocq's binary N. The
   src/ of the fix's parent leaves the whole argument as it is when a Fin pair of the argument has other values, so
   the kernel converts the Nat pair on the unary Nat, one successor at a time, and the entry is refused at the
   10 s limit below (ci/build-9.2-cut.sh --revert-fix). tests/fin_transport_values_differ.expect checks the log. *)
Set Warnings "+unknown-option".
Set Lean Entry Timeout 10.
Set Lean Error Mode "Skip".
Redirect "fin_transport_values_differ.log" Lean Import "../dumps/lean434/fin_values.ndjson".

Check RLI434V_values_differ.
Check RLI434V_values_differ__nat_eq_1.
