From Stdlib Require Import NArith.
From LeanImport Require Import Lean.
From Test Require Import rocqchk_literal_form.

(* Natural literals below 2^62 and refused ones, from dumps/lean434/rocqchk_literal.ndjson (tests/Makefile runs
   rocqchk on this test's .vo, ROCQCHK_TESTS). The importer keeps a literal as the decimal string of its value
   (src/leanExpr.mli, Nat), and Lean Import stores its state in the .vo; below 2^62 a Zarith value was an immediate
   int, so rocqchk read this .vo before that change too. The literals 2^62 and 2^62 + 1 are tests/rocqchk_literal.v
   and tests/rocqchk_literal_over.v. tests/rocqchk_literal_below.expect checks the logs. *)
Set Lean Error Mode "Skip".
(* Lines 1-76: Nat, then a def of type Nat per literal: 0, 1, 4999, 5000, 2^62 - 1, "7", "007" and the JSON
   integer 7. *)
Redirect "rocqchk_literal_below.log" Lean Import "../dumps/lean434/rocqchk_literal.ndjson" 1 77.

Check (Logic.eq_refl : Logic.eq RLIChk_zero 0%Nat).
Check (Logic.eq_refl : Logic.eq RLIChk_one 1%Nat).
Check (Logic.eq_refl : Logic.eq RLIChk_n4999 4999%Nat).
Check (Logic.eq_refl : Logic.eq RLIChk_seven 7%Nat).
(* "007" and the JSON integer 7 give the same canonical string as "7", so the same term. *)
Check (Logic.eq_refl : Logic.eq RLIChk_seven_zeros RLIChk_seven).
Check (Logic.eq_refl : Logic.eq RLIChk_seven_int RLIChk_seven).
(* From 5000 on, the importer's binary form (tests/rocqchk_literal_form.v). *)
Definition rocqchk_form_5000 : Nat := Eval cbv -[LeanImport.Lean.double] in rocqchk_lit 5000.
Definition rocqchk_form_below : Nat :=
  Eval cbv -[LeanImport.Lean.double] in rocqchk_lit 4611686018427387903.
Timeout 60 Check (Logic.eq_refl : Logic.eq RLIChk_n5000 rocqchk_form_5000).
Timeout 60 Check (Logic.eq_refl : Logic.eq RLIChk_below rocqchk_form_below).

(* Lines 83-107, after the prefix 1-82 (read for its names and expressions only, so the literals 2^62 and 2^62 + 1
   of lines 78 and 81 stay in the NDJSON parser's state, which Lean Import does not store): line 83, the literal
   2^64 that no entry uses; line 89, RLIChk.refused_big, whose value applies the undeclared RLIChk.missing to the
   literal 2^64 + 1, refused, so that its entry is not stored either; lines 90-107, six literals and a def using
   each: "-1", "x7", the JSON integers -1 and 2^62 (beyond OCaml's int) and null are refused; "" is read by Zarith
   as 0, as it was before literals were kept as strings. *)
Redirect "rocqchk_literal_below_refused.log" Lean Import "../dumps/lean434/rocqchk_literal.ndjson" 83.

Check (Logic.eq_refl : Logic.eq RLIChk_empty_str 0%Nat).
Fail Check RLIChk_refused_big.
Fail Check RLIChk_neg_str.
Fail Check RLIChk_null_val.
