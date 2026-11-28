From LeanImport Require Import Lean.

(* Literal arithmetic, the lemmas the kernel refuses (README, "Transport of proof arguments across Nat
   literals"): a refused lemma, a hole's or a sub-lemma generated while the holes are found, leaves its whole
   argument to Lean's term, and no refusal is remembered. dumps/lean434/litarith_planted.ndjson is
   dumps/lean434/litarith.ndjson with Lean's Nat.mod and Nat.pred renamed Nat.modLib and Nat.predLib and the
   fixtures' pmod and ppred named Nat.mod and Nat.pred, of the values fun _ _ => 0 and fun n => n (its row in
   dumps/lean434/README.md); it is the only export of this document, so that the pass reads the planted names.
   It imports the definitions (lines 1 to 23878), then the theorems of lines 24673 to 24713:
   - refused_hole (24685): Q2 65536 mk_k1 mk_k2 against Q2 65536 (1, 65567) (2, 65567), mk_k1 = (Nat.mod 7 3,
     65536 + 31): the evaluation reads 1 for Nat.mod 7 3, the kernel computes the planted Nat.mod to 0, so the
     first place's lemma is refused: one refusal line, the argument keeps Lean's term and the second place's
     lemma is not generated; the kernel then refuses the entry with Lean's value at the planted Nat.mod; the
     test's own entry, which the src/ of the fix's parent refuses too, with no refusal line;
   - refused_sub (24696): (0, 65536 - 31) beside the Nat place 4999 + 1 against 5000: the Sub row's lemma takes
     the planted Nat.pred, whose toN_pred instance the kernel refuses: the refusal line, and the whole argument
     keeps Lean's term (the Nat place too); the kernel converts the pair with Lean's own Nat.sub;
   - refused_twice (24709): mk_k1 against (1, 65567) in the two arguments of And.intro: two refusal lines;
     refused_again (24713): the same pair again in another entry: one more;
   - refused_shared (26063, after the lines of every other test): the same pair in the two explicit arguments of
     both {p} (a b : p), whose domains are the one term p and whose types are h's: the pair of the second argument
     is the first's, physically, and is checked again: two refusal lines.
   tests/litarith_refused.expect checks the logs. *)
Set Warnings "+unknown-option".
Set Lean Error Mode "Skip".
Set Lean Entry Timeout 10.
Redirect "litarith_refused_lib.log" Lean Import "../dumps/lean434/litarith_planted.ndjson" 1 23879.
Redirect "litarith_refused.log" Lean Import "../dumps/lean434/litarith_planted.ndjson" 24673 24714.
Redirect "litarith_refused_shared.log" Lean Import "../dumps/lean434/litarith_planted.ndjson" 26051 26064.

(* Every lemma a cast above uses exists; a lemma the kernel refused was not declared. *)
Check RLI434L_mpf_a__proof_1__nat_eq_1.
Check RLI434L_mpf_a__proof_2__nat_eq_1.
Fail Check RLI434L_refused_hole__nat_eq_2.
Fail Check RLI434L_refused_sub__nat_eq_1.
Fail Check RLI434L_refused_twice__nat_eq_2.
Fail Check RLI434L_refused_twice__nat_eq_3.
Fail Check RLI434L_refused_again__nat_eq_2.
