From LeanImport Require Import Lean.

(* A natural literal of 2^64 that no entry uses, in an export of the old text format: dumps/rocqchk_literal_text,
   line 10. Lean Import stores the text parser's state, every expression parsed so far included, in the .vo, and
   tests/Makefile runs rocqchk on this test's .vo (ROCQCHK_TESTS). Before the importer kept a literal as the decimal
   string of its value (src/leanExpr.mli, Nat), rocqchk refused it ("Unhandled code 0018"); its row in
   tests/lean434_features.txt is check:rocqchk. A text literal an entry uses is tests/core.v's (dumps/core line
   11195, UInt64.size). tests/rocqchk_literal_text.expect checks the log. *)
Set Lean Error Mode "Skip".
(* Line 14: RLIChkText.seven, written "#ELN 007"; line 15, a literal that is not a number, refused, and line 17,
   the def that uses it; line 20, RLIChkText.neg, whose literal -1 the text parser accepts, refused where its term
   is built. *)
Redirect "rocqchk_literal_text.log" Lean Import "../dumps/rocqchk_literal_text".

Check (Logic.eq_refl : Logic.eq RLIChkText_seven 7%Nat).
Fail Check RLIChkText_bad.
Fail Check RLIChkText_neg.
