From LeanImport Require Import Lean.

(* Literal arithmetic with names of the export absent (README, "Transport of proof arguments across Nat
   literals"): each list the pass reads in setup may be empty, which turns off the mechanism that needs it and
   nothing else. dumps/lean434/litarith_absent.ndjson is dumps/lean434/litarith.ndjson with Nat.pred,
   Nat.div_eq_of_lt_le, decide_eq_true, Dvd.dvd, Int.le, Nat.beq, Nat.ble and Nat.mod renamed with the suffix Lib
   (its row in dumps/lean434/README.md); it is the only export of this document, since the pass's lists of the
   export's constants of a name are document-wide. It imports the definitions (lines 1 to 23878), then:
   - own_mul (23889): some (4294967296 * 2) against some 8589934592, cast by the Mul row's certificate, which
     needs none of the renamed names; the test's own entry, which the src/ of the fix's parent leaves to the
     kernel, refused at the 10 s limit;
   - dvd_256 (24570): decide (256 ∣ 4294967296) with Dvd.dvd absent: no proof, no line, and the kernel's
     check of the divisibility refused at the 10 s limit;
   - sub_held_a (24715): 65536 - 31 against 65505 with no Nat.pred: no sub-lemma, no line; div_held_a (24717):
     65536 / 64 with no Nat.div_eq_of_lt_le: no line; mod_65536_a (24725): 65536 % 7 with no Nat.mod, which
     unfolds to Lean's Nat.modLib and its first comparison Nat.ble 7 65536 is no comparison the pass reads either:
     no line; beq_small_a (24732): Nat.beq 65535 65535 with no Nat.beq, which unfolds: no line; nonneg_a (24740):
     0 ≤ Int.ofNat 65536 with no Int.le: no proof, no line; le_big_a (24746): 65536 ≤ 65536 + 1 with no
     decide_eq_true: no lemma for the decide, no line. No entry fails the pass.
   tests/litarith_absent.expect checks the logs. *)
Set Warnings "+unknown-option".
Set Lean Error Mode "Skip".
Set Lean Entry Timeout 10.
Redirect "litarith_absent_lib.log" Lean Import "../dumps/lean434/litarith_absent.ndjson" 1 23879.
Redirect "litarith_absent_own.log" Lean Import "../dumps/lean434/litarith_absent.ndjson" 23879 23890.
Redirect "litarith_absent_dvd.log" Lean Import "../dumps/lean434/litarith_absent.ndjson" 24559 24571.
Redirect "litarith_absent.log" Lean Import "../dumps/lean434/litarith_absent.ndjson" 24714 24747.

(* Every lemma a cast above uses exists; a lemma the kernel refused was not declared. *)
Check RLI434L_own_mul__nat_eq_2.
