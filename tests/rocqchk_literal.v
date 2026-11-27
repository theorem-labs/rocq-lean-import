From Stdlib Require Import NArith.
From LeanImport Require Import Lean.
From Test Require Import rocqchk_literal_form.

(* The natural literal 2^62 = 4611686018427387904, the smallest that a Zarith value holds in a custom block: the
   def RLIChk.limit of dumps/lean434/rocqchk_literal.ndjson (line 79). Lean Import stores its state, this entry
   included, in the .vo, and tests/Makefile runs rocqchk on this test's .vo (ROCQCHK_TESTS). Before the importer
   kept a literal as the decimal string of its value (src/leanExpr.mli, Nat), rocqchk refused the .vo
   ("Unhandled code 0018"); its row in tests/lean434_features.txt is decided by that step (check:rocqchk). The
   literal 2^62 - 1 is tests/rocqchk_literal_below.v, 2^62 + 1 tests/rocqchk_literal_over.v. *)
Set Lean Error Mode "Fail".
(* Lines 1-51: Nat; then line 79, after the prefix 1-76 (read for its names and expressions only). *)
Lean Import "../dumps/lean434/rocqchk_literal.ndjson" 1 52.
Lean Import "../dumps/lean434/rocqchk_literal.ndjson" 77 80.

(* The term is the importer's form of the value (tests/rocqchk_literal_form.v). *)
Definition rocqchk_form_limit : Nat :=
  Eval cbv -[LeanImport.Lean.double] in rocqchk_lit 4611686018427387904.
Timeout 60 Check (Logic.eq_refl : Logic.eq RLIChk_limit rocqchk_form_limit).
