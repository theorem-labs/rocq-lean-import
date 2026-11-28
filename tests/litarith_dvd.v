From LeanImport Require Import Lean.

(* Literal arithmetic, a held decide (README, "Transport of proof arguments across Nat literals"): a closed
   decide p whose proposition holds a Nat term of 65536 or more is held as a whole; its value true is proved by
   Lean's decide_eq_true from a proof of p: a ∣ b at Nat by the witness b / a, otherwise p reduced at its head
   (at most 64 steps from 0) to Nat_le, to eq at Nat or at another data type (a nested evaluation), or to Lean's
   Int.NonNeg x. dumps/lean434/litarith.ndjson: the definitions (lines 1 to 23878), then this test's theorems
   (lines 24559 to 24672). Cast:
   - dvd_256 (24570): decide (256 ∣ 4294967296) against true at Lean's Bool (helper₃'s lemma _3); the test's own
     entry, which the src/ of the fix's parent leaves to the kernel, refused at the 10 s limit;
   - dvd_zero_sub (24586): decide (0 ∣ 65536 - 65536), whose only large term is replaced by 0 in the first round;
   - le_big (24594), le_eq (24602): 65536 ≤ 65536 + 1 and 65536 ≤ 65536; eq_nat (24610): 65536 * 2 = 2 * 65536;
     eq_data (24618): (65536 - 1, 1) = (65535, 1), a nested evaluation; nonneg (24626): 0 ≤ Int.ofNat 65536;
   - fb12_63 (24642), fb12_64 (24648): a proposition that reaches 65536 = 65536 after 63 and 64 head steps;
   - nested_stop (24664): a nested evaluation that meets a stuck eliminator, which ends the nested proof only;
   - eq_nat_l (26021) and nonneg_l (26043), after the lines of every other test: eq_nat's and nonneg's decide at
     2 ^ 33 (4294967296 * 2 = 2 * 4294967296, 0 ≤ Int.ofNat (4294967296 * 2)), whose sides the kernel cannot
     compute within the entry's limit: each proof must state its sides in the decide's own order.
   - chain_nested (26603), after the lines of every other test: cond (decide (0 ≤ Int.ofNat 65536 - 1)) 1 0 in the
     pair's first field: the held decide's proof evaluates Int.ofNat 65536 - 1 in a nested evaluation, where
     Int.add's match waits on Int.subNatNat's fixpoint, which waits on the held 1 - 65536 (a chain of waits); the
     nested round 1 gives Int.ofNat 65535, the decide gets true and the outer cond contracts in round 1. The src/ of
     the fix's parent ends the nested proof at that chain (the third class), with no lemma and no line.
   No line, the entry declared:
   - dvd_zero (24578): a divisor 0, no proof; nonneg_neg (24634): 0 ≤ Int.negSucc 65536, no proof; fb12_65
     (24654): 65 head steps, no proof; nested_wait (24672): nested_stop's decide under a match that waits on it.
   tests/litarith_dvd.expect checks the logs. *)
Set Warnings "+unknown-option".
Set Lean Error Mode "Skip".
Set Lean Entry Timeout 10.
Redirect "litarith_dvd_lib.log" Lean Import "../dumps/lean434/litarith.ndjson" 1 23879.
Redirect "litarith_dvd.log" Lean Import "../dumps/lean434/litarith.ndjson" 24559 24673.
Redirect "litarith_dvd_l.log" Lean Import "../dumps/lean434/litarith.ndjson" 25998 26044.

(* A chain of waits: the lines 26220 to 26671 of dumps/lean434/litarith.ndjson, every line of them but the theorem
   lines of the other tests (the definitions and chain_nested's line 26603), after every other range of this test.
   They come before every Check, so that a lemma a change of the pass loses cannot stop the file before these logs
   are made. *)
Redirect "litarith_dvd_chain_0.log" Lean Import "../dumps/lean434/litarith.ndjson" 26220 26456.
Redirect "litarith_dvd_chain_1.log" Lean Import "../dumps/lean434/litarith.ndjson" 26457 26462.
Redirect "litarith_dvd_chain_2.log" Lean Import "../dumps/lean434/litarith.ndjson" 26463 26468.
Redirect "litarith_dvd_chain_3.log" Lean Import "../dumps/lean434/litarith.ndjson" 26469 26488.
Redirect "litarith_dvd_chain_4.log" Lean Import "../dumps/lean434/litarith.ndjson" 26489 26501.
Redirect "litarith_dvd_chain_5.log" Lean Import "../dumps/lean434/litarith.ndjson" 26502 26524.
Redirect "litarith_dvd_chain_6.log" Lean Import "../dumps/lean434/litarith.ndjson" 26525 26537.
Redirect "litarith_dvd_chain_7.log" Lean Import "../dumps/lean434/litarith.ndjson" 26538 26545.
Redirect "litarith_dvd_chain_8.log" Lean Import "../dumps/lean434/litarith.ndjson" 26546 26553.
Redirect "litarith_dvd_chain_9.log" Lean Import "../dumps/lean434/litarith.ndjson" 26554 26561.
Redirect "litarith_dvd_chain_10.log" Lean Import "../dumps/lean434/litarith.ndjson" 26562 26567.
Redirect "litarith_dvd_chain_11.log" Lean Import "../dumps/lean434/litarith.ndjson" 26568 26573.
Redirect "litarith_dvd_chain_12.log" Lean Import "../dumps/lean434/litarith.ndjson" 26574 26579.
Redirect "litarith_dvd_chain_13.log" Lean Import "../dumps/lean434/litarith.ndjson" 26580 26589.
Redirect "litarith_dvd_chain_14.log" Lean Import "../dumps/lean434/litarith.ndjson" 26590 26597.
Redirect "litarith_dvd_chain_15.log" Lean Import "../dumps/lean434/litarith.ndjson" 26598 26609.
Redirect "litarith_dvd_chain_16.log" Lean Import "../dumps/lean434/litarith.ndjson" 26610 26653.
Redirect "litarith_dvd_chain_17.log" Lean Import "../dumps/lean434/litarith.ndjson" 26654 26659.
Redirect "litarith_dvd_chain_18.log" Lean Import "../dumps/lean434/litarith.ndjson" 26660 26671.

(* Every lemma a cast above uses exists; a lemma the kernel refused was not declared. *)
Check RLI434L_dvd_256__nat_eq_2.
Check RLI434L_dvd_zero_sub__nat_eq_3.
Check RLI434L_le_big__nat_eq_1.
Check RLI434L_le_eq__nat_eq_1.
Check RLI434L_eq_nat__nat_eq_2.
Check RLI434L_eq_data__nat_eq_2.
Check RLI434L_nonneg__nat_eq_2.
Check RLI434L_fb12_63__nat_eq_2.
Check RLI434L_fb12_64__nat_eq_1.
Check RLI434L_nested_stop__nat_eq_1.
Check RLI434L_mpf_a__proof_1__nat_eq_1.
Check RLI434L_mpf_a__proof_2__nat_eq_1.

(* The lemma the cast of chain_nested uses exists. *)
Check RLI434L_chain_nested__nat_eq_3.
