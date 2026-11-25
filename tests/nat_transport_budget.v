From LeanImport Require Import Lean.

(* The work of the transport pass is bounded per entry (README, "Transport of proof arguments across Nat
   literals"). dumps/lean434/nat_budget.ndjson declares RLI434D1.c15 := 1 and, for k from 14 to 0,
   RLI434D1.ck := c(k+1) + ... + c(k+1) (Nat.add, 8 terms), so c0 = 8^15: a value finder that evaluates every
   occurrence of a constant makes about 8^15 steps. tests/nat_transport_budget.expect checks the log. *)
Set Lean Error Mode "Skip".
Set Warnings "+unknown-option".
Set Lean Entry Timeout 5.
Redirect "nat_transport_budget.log" Lean Import "../dumps/lean434/nat_budget.ndjson".

(* RLI434D1.refl : c0 = c0 := Eq.refl c0: the pass computes c0's value (each constant once) and finds no
   place to transport; the entry imports at once. *)
Check RLI434D1_refl.
(* RLI434D1.lit : c0 = 35184372088832 := Eq.refl c0: the certificate of c0 would be a tree of about 8^15
   steps, so the pass stops at its step budget and leaves Lean's value, which the kernel refuses (it compares
   c0 with the literal one Nat_succ at a time). *)
Fail Check RLI434D1_lit.
