From LeanImport Require Import Lean.

(* A listed feature: the test checks that its entries are refused and that the import goes on to its end
   (tests/lean434_string_length.expect). RLI434.ab_length ("ab".length = 2 := rfl) needs String.length, which
   stands behind Lean's Nat.mul_add_div._f: a Nat.Linear reflection proof whose check evaluates Lean's Nat.beq
   and Nat.blt on the literal 100000000 one Nat_succ at a time (it imports in about 26 minutes with a large
   enough Lean Entry Timeout, not within this test's 5 s). When a change makes these entries import, this test
   fails: the feature is then fixed, and its row in tests/lean434_features.txt moves to fixed. *)
Set Lean Error Mode "Skip".
Set Warnings "+unknown-option".
Set Lean Entry Timeout 5.
Redirect "lean434_string_length.log" Lean Import "../dumps/lean434/strings.ndjson".
