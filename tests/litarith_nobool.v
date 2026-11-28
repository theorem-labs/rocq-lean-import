From LeanImport Require Import Lean.

(* Literal arithmetic with no Lean Bool to read (README, "Transport of proof arguments across Nat literals"):
   the pass reads Lean's Bool from the declared type of Decidable.decide. dumps/lean434/litarith_nobool.ndjson
   is dumps/lean434/litarith.ndjson with Decidable.decide renamed Decidable.decideLib and nothing else (its row in
   dumps/lean434/README.md); it is the only export of this document. It imports the definitions (lines 1 to
   23878), then:
   - own_mul (23889): cast by the Mul row's certificate, which needs no Bool; the test's own entry, which the
     src/ of the fix's parent leaves to the kernel, refused at the 10 s limit;
   - beq_small_t (24395): Nat.beq 65535 65535 with no Bool constructor to write: the comparison unfolds, each
     step charged: no line;
   - dvd_256 (24570): no decide is held; its unfolding reaches a held 4294967296 % 256: no line, and the kernel's
     check of the divisibility refused at the 10 s limit.
   tests/litarith_nobool.expect checks the logs. *)
Set Warnings "+unknown-option".
Set Lean Error Mode "Skip".
Set Lean Entry Timeout 10.
Redirect "litarith_nobool_lib.log" Lean Import "../dumps/lean434/litarith_nobool.ndjson" 1 23879.
Redirect "litarith_nobool_own.log" Lean Import "../dumps/lean434/litarith_nobool.ndjson" 23879 23890.
Redirect "litarith_nobool_beq.log" Lean Import "../dumps/lean434/litarith_nobool.ndjson" 24389 24396.
Redirect "litarith_nobool_dvd.log" Lean Import "../dumps/lean434/litarith_nobool.ndjson" 24559 24571.

(* Every lemma a cast above uses exists; a lemma the kernel refused was not declared. *)
Check RLI434L_own_mul__nat_eq_2.
