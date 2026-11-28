From Stdlib Require Import NArith.
From LeanImport Require Import Lean.
From Test Require Import rocqchk_literal_form.

(* The natural literal 2^62 + 1 = 4611686018427387905, one above the limit of tests/rocqchk_literal.v: the def
   RLIChk.over of dumps/lean434/rocqchk_literal.ndjson (line 82). tests/Makefile runs rocqchk on this test's .vo
   (ROCQCHK_TESTS), which rocqchk refused before literals were strings (why: lean_obj in src/lean.ml); its row in
   tests/lean434_features.txt is check:rocqchk. *)
Set Lean Error Mode "Fail".
(* Lines 1-51: Nat; then line 82, after the prefix 1-79. *)
Lean Import "../dumps/lean434/rocqchk_literal.ndjson" 1 52.
Lean Import "../dumps/lean434/rocqchk_literal.ndjson" 80 83.

Definition rocqchk_form_over : Nat :=
  Eval cbv -[LeanImport.Lean.double] in rocqchk_lit 4611686018427387905.
Timeout 60 Check (Logic.eq_refl : Logic.eq RLIChk_over rocqchk_form_over).
