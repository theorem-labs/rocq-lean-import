From LeanImport Require Import Lean.

(* Literal arithmetic, the evaluator's rule (README, "Transport of proof arguments across Nat literals"): a place
   of two closed terms of a data type with different heads, which the pass evaluates in rounds, holding each Nat
   operation of 65536 or more, and proves equal by a lemma a = d at their type. dumps/lean434/litarith.ndjson is
   exported from dumps/lean434/src/RLI434LitArith.lean; its lines 1 to 23878 are the definitions every
   litarith test imports first, and this test's theorems are lines 23890 to 24190. Each theorem passes a proof
   of Q 65536 a where Q 65536 d is expected; most pairs are mk_x against mk_x' at a type _ × Nat whose second
   fields are 65536 - 31 against 65505, a held subtraction whose sub-lemma gives the pair a proof to make.
   Cast:
   - tidy_big (23923): omega's tidyConstraint on Int literals near 2 ^ 32 and a coefficient of 4096, the assemble
     roots' own form (the roots' lemma _5; the importer writes 4096 unary, below 5000): the pair's lemma at omega's
     Constraint, through sprop_transport_any; the test's own entry, which the src/ of the fix's parent leaves to
     the kernel, refused at the 10 s limit;
   - c_match (23933), c_fix (23941), c_proj (23949): a match, a fixpoint and a projection on a constructor;
     c_match_f (26076, after the lines of every other test): cond false 0 1, the branch of Bool's first
     constructor;
   - w_fix (23968): Int.subNatNat 65536 32 against Int.ofNat 65504, a fixpoint waiting on the held 32 - 65536 for
     one round (the roots' case); w_fix_dep (23978): a dependent eliminator of a structure Pk waiting on
     65536 - 1, whose return predicate, branches and dependent field hold the held 65536 + 1;
   - w_match (23996): a match waiting on a held decide (256 ∣ 256 * 65536), proved in the next round;
   - s_head (24046): an axiom's application, its own weak head normal form; s_param (24056): a stuck eliminator
     in a lambda's body, a position the evaluation does not evaluate;
   - values_differ_l (24113): two sides of different values (some 0 against some 1) under ign, beside the Nat
     place 4999 + 1 against 5000: no lemma for the first pair, the Nat place cast;
   - same_heads (24121): some (65536 - 31) against some 65505, the same heads: the lemma at Nat of the place
     inside; open_pair_l (24132): x + (65536 - 31) against x + 65505 under a forall: the closed place inside;
   - rounds_15 (24160) and rounds_16 (24173): 15 and 16 replacement rounds, both places cast; rounds_17
     (24190): 17 rounds, the replacement field's lemma alone. The three are imported on their own at an Entry
     Timeout of 60 s: with no lemma for the first place, the kernel computes 17 x - 65536 steps on the unary
     Nat (12.4 s on the narrowed prototype).
   No line, the entry declared (the kernel converts the pair as without the pass):
   - w_unresolved (24004) and e_memo (24014): a wait no round resolves (257 does not divide 256 * 65536), the
     second time a memo hit of the same round; s_match (24022), s_fix (24030), s_proj (24038): a match, a
     fixpoint and a projection on an axiom (the third class); field_unvalued (24064): axN + 3, an operand with
     no value; nothing_held (24074): on1 3 against on2 3, nothing held; unknown_param (24086): parameters Fin
     (1 + 1) and Fin 2, normal forms of no known order; type_fun (24142): two functions, a type whose sort the
     bounded query does not read; type_fun_held (25997, after the lines of every other test): tfa against tfd at
     Nat → Nat, tfa a match on le_big's held decide (65536 ≤ 65536 + 1) that a round decides, so that its
     evaluation holds an operation at an evaluated position and only the unread sort leaves the pair no hole.
   A refusal line, no transported line, the entry declared:
   - motive_proof (23988): the cast's motive abstracts the held 65536 + 1 inside the pair's type Fin (65536 + 1)
     and inside a proof by decide; the kernel refuses the pair's lemma and the argument keeps Lean's term.
   tests/litarith_eval.expect checks the logs. *)
Set Warnings "+unknown-option".
Set Lean Error Mode "Skip".
Set Lean Entry Timeout 10.
Redirect "litarith_eval_lib.log" Lean Import "../dumps/lean434/litarith.ndjson" 1 23879.
Redirect "litarith_eval.log" Lean Import "../dumps/lean434/litarith.ndjson" 23890 24143.
Set Lean Entry Timeout 60.
Redirect "litarith_eval_rounds.log" Lean Import "../dumps/lean434/litarith.ndjson" 24143 24191.
Set Lean Entry Timeout 10.
Redirect "litarith_eval_type_fun_held.log" Lean Import "../dumps/lean434/litarith.ndjson" 25981 25998.
Redirect "litarith_eval_c_match_f.log" Lean Import "../dumps/lean434/litarith.ndjson" 26064 26077.

(* Every lemma a cast above uses exists; a lemma the kernel refused was not declared. *)
Check RLI434L_tidy_big__nat_eq_2.
Check RLI434L_c_match__nat_eq_2.
Check RLI434L_c_fix__nat_eq_1.
Check RLI434L_c_proj__nat_eq_1.
Check RLI434L_w_fix__nat_eq_3.
Check RLI434L_w_fix_dep__nat_eq_3.
Check RLI434L_w_match__nat_eq_2.
Check RLI434L_s_head__nat_eq_1.
Check RLI434L_s_param__nat_eq_1.
Check RLI434L_values_differ_l__nat_eq_1.
Check RLI434L_same_heads__nat_eq_1.
Check RLI434L_mpf_a__proof_1__nat_eq_1.
Check RLI434L_mpf_a__proof_2__nat_eq_1.
Check RLI434L_rounds_15__nat_eq_31.
Check RLI434L_rounds_16__nat_eq_4.
Fail Check RLI434L_motive_proof__nat_eq_2.

(* Row V-heads: same_heads's lemma is the place inside, 65536 - 31 = 65505 at Nat, not the two sides at Option Nat
   (its statement names no Option); open_pair_l's place under the binder is the same pair, and uses that lemma. *)
Redirect "litarith_eval_same_heads.log" Check RLI434L_same_heads__nat_eq_1.

(* The lemmas of src/Lean.v that literal arithmetic adds: those on toN rely on nothing, the cast at any type and
   toN_of_eq only on the definitional UIP of eq (as every entry that names eq does). The generated lemma of
   tidy_big holds 4294967296 / 4096, so it also relies on what Lean's Nat.div_eq_of_lt_le relies on (the
   sub-lemma of a held division, M7): the definitional UIP, and propext with the sort eliminations of Iff. *)
Definition litarith_toN_lemmas : unit := let _ := @toN_pred in let _ := @toN_sub in let _ := @toN_nat in
  let _ := @Nat_le_of_toN in tt.
Redirect "litarith_eval_assumptions_toN.log" Print Assumptions litarith_toN_lemmas.
Definition litarith_uip_lemmas : unit := let _ := @toN_of_eq in let _ := @sprop_transport_any in tt.
Redirect "litarith_eval_assumptions_uip.log" Print Assumptions litarith_uip_lemmas.
Redirect "litarith_eval_assumptions_tidy.log" Print Assumptions RLI434L_tidy_big__nat_eq_2.
Redirect "litarith_eval_assumptions_div.log" Print Assumptions Nat_div_eq_of_lt_le.
