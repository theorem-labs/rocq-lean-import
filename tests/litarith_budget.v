From LeanImport Require Import Lean.

(* Literal arithmetic and the step budget (README, "Lean Transport Step Budget"): every step of the evaluation is
   charged to the part, to the entry's total and to the pair's cap of 200000 steps, which declines the pair (its
   steps stay in the argument's part, and no pair inside it is evaluated again). dumps/lean434/litarith.ndjson: the
   definitions (lines 1 to 23878), the budget entries below by
   their own lines; dumps/lean434/litarith_deep.ndjson (litarith.ndjson and the lines of its row appended, from
   line 45911): the chain of 1218 constants of each side that row E-cap needs and the deep nest of row
   D-depth. Every budget below is measured from the counters of this file at every part's default budget (Job of
   its row in the port's report); the three runs of one entry are at its largest part - 1, at it and + 1.
   - E-step, B-part: bud_tidy (tidy_big's shape on terms of its own; its argument part 45,230), bud_dvd (dvd_256's shape;
     20,640) and bud_hold (h_operand's shape; 5,586): the stop line one step below the part, the cast at the part and
     above, and the cast at the default. The kernel's check of Lean's value, after a stop, outlasts the 10 s limit.
   - X-lit: lit_5000 (a held 65536 - 60536, where the importer's literal changes form) at its argument part 5,170.
   - B-total: bud_total, thirty-three arguments each a pair of its own, next to an entry part smaller than one argument's:
     all the parts together take 1,921,226 steps; at N = 192,123 (10 N above that) it casts, at N - 1 the pass stops
     for the entry ("more than 10 (N - 1) steps in total"), as nat_transport_total.v does for the Nat case's.
   - E-loop (loop_head: Nat.repeat id 4294967296 0 on both sides, a fixpoint that does not end within the pair's
     cap), N-cap (nested_cap: the nested evaluation of a decide's proposition alone needs more than the cap), E-share
     (expo_share, the closed substitution's row: dupT applied 60 times, each argument shared
     by the two sons of the next, 2 ^ 60 nodes as a tree and 61 as a graph; the evaluation walks it as a tree and
     stops at the cap): no lemma and no line; the kernel converts the two sides (the first fields are the same term).
   - B-order-pair, B-total-pair: order_pair (one pair of more than the cap, in the entry's own result) at
     N = D + 200000, D the part's debit when the pair starts, and order_total (nine arguments of pairs declined at the
     cap, then the same pair in the result; ten fixtures, order_total to order_total_j, whose last argument's literal adds
     1 to S each (the entry's walk takes the literal whole), so that S + 200000 divides by 10: order_total_e) at N = (S + 200000) / 10, S the entry's total debit then: one charge takes
     the pair and the part (or the total) below zero together, and the part (or the total) is tested first, so the
     pass stops with its line.
   - E-cap, E-cap-next: the pair of a chain of constants (dl_1217 against dr_1217, behind a few applications of idl,
     idl2 and idl3 that adjust the count): needs 200001 steps and is declined (cap_hi, no lemma), 200000 (cap_at) and
     199999 (cap_lo) and casts. cap_next puts the declined pair of the first with one of about two thirds of its
     steps in one argument: the second casts, the counter starting again at each outer pair. The count of an entry
     depends on the lemmas declared before it (the cache of a file), so the runs are in this order.
   - D-depth: deep_lo, deep_at and deep_hi, dwrap applied 9961, 9962 and 9963 times to a pair: the nesting the
     pass follows reaches 9999, 10000 and 10001 levels; the first two cast, the third stops the pass (nothing else
     descends into the evaluation: its own nesting is about 40 levels).
   - The proof's tree: proof_size (dupT applied 4 times over a held 70535 - 65536, so that the last round puts the
     literal 4999, about 10000 nodes as a tree, at 16 places of the final normal form): the pair's walks stay far
     below the cap, the tree size of its proof's evaluated terms does not, so it is declined (no lemma, no line).
   - A nest of declined pairs: nest_capped (nf1 (... (nf5 ncA)) against ng1 (... (ng5 100)), ncA's evaluation alone
     more than the cap, beside the Nat place 2 ^ 32 against 4294967296): the outermost pair is declined and no pair
     inside it is evaluated, so the Nat place casts (six declines would take the part past its budget).
   tests/litarith_budget.expect checks the logs. *)
Set Warnings "+unknown-option".
Set Lean Error Mode "Skip".
Set Lean Entry Timeout 10.
Redirect "litarith_budget_lib.log" Lean Import "../dumps/lean434/litarith.ndjson" 1 23879.
Redirect "litarith_budget_defs_0.log" Lean Import "../dumps/lean434/litarith.ndjson" 24766 24782.
Redirect "litarith_budget_defs_1.log" Lean Import "../dumps/lean434/litarith.ndjson" 25340 25455.
Redirect "litarith_budget_defs_2.log" Lean Import "../dumps/lean434/litarith.ndjson" 25463 25661.
Redirect "litarith_budget_defs_3.log" Lean Import "../dumps/lean434/litarith.ndjson" 25669 25676.
Redirect "litarith_budget_defs_4.log" Lean Import "../dumps/lean434/litarith.ndjson" 25684 25696.
Redirect "litarith_budget_defs_5.log" Lean Import "../dumps/lean434/litarith.ndjson" 25732 25856.
Redirect "litarith_budget_defs_6.log" Lean Import "../dumps/lean434/litarith.ndjson" 25866 25885.
Redirect "litarith_budget_defs_7.log" Lean Import "../dumps/lean434/litarith.ndjson" 25981 25990.
Redirect "litarith_budget_defs_8.log" Lean Import "../dumps/lean434/litarith.ndjson" 25998 26014.
Redirect "litarith_budget_defs_9.log" Lean Import "../dumps/lean434/litarith.ndjson" 26022 26036.
Redirect "litarith_budget_defs_10.log" Lean Import "../dumps/lean434/litarith.ndjson" 26064 26071.
Redirect "litarith_budget_defs_11.log" Lean Import "../dumps/lean434/litarith.ndjson" 26077 26085.
Redirect "litarith_budget_defs_12.log" Lean Import "../dumps/lean434/litarith.ndjson" 26100 26133.
Redirect "litarith_budget_defs_13.log" Lean Import "../dumps/lean434/litarith.ndjson" 26146 26164.
Redirect "litarith_budget_defs_14.log" Lean Import "../dumps/lean434/litarith.ndjson" 26172 26192.

Redirect "litarith_budget_chain.log" Lean Import "../dumps/lean434/litarith_deep.ndjson" 85774 97964.
Redirect "litarith_budget_cap_next.log" Lean Import "../dumps/lean434/litarith_deep.ndjson" 98050 98051.
Redirect "litarith_budget_cap_hi.log" Lean Import "../dumps/lean434/litarith_deep.ndjson" 97985 97986.
Redirect "litarith_budget_cap_lo.log" Lean Import "../dumps/lean434/litarith_deep.ndjson" 98000 98001.
Redirect "litarith_budget_cap_at.log" Lean Import "../dumps/lean434/litarith_deep.ndjson" 98024 98025.
Redirect "litarith_budget_deep_lo.log" Lean Import "../dumps/lean434/litarith_deep.ndjson" 45911 45912.
Redirect "litarith_budget_deep_at.log" Lean Import "../dumps/lean434/litarith_deep.ndjson" 65841 65842.
Redirect "litarith_budget_deep_hi.log" Lean Import "../dumps/lean434/litarith_deep.ndjson" 85773 85774.

Set Lean Transport Step Budget 5170.
Redirect "litarith_budget_lit5000.log" Succeed Lean Import "../dumps/lean434/litarith.ndjson" 24337 24338.
Unset Lean Transport Step Budget.

Set Lean Transport Step Budget 45229.
Redirect "litarith_budget_bud_tidy_stop.log" Succeed Lean Import "../dumps/lean434/litarith.ndjson" 24765 24766.
Set Lean Transport Step Budget 45230.
Redirect "litarith_budget_bud_tidy_part.log" Succeed Lean Import "../dumps/lean434/litarith.ndjson" 24765 24766.
Set Lean Transport Step Budget 45231.
Redirect "litarith_budget_bud_tidy_over.log" Succeed Lean Import "../dumps/lean434/litarith.ndjson" 24765 24766.
Unset Lean Transport Step Budget.
Redirect "litarith_budget_bud_tidy.log" Lean Import "../dumps/lean434/litarith.ndjson" 24765 24766.

Set Lean Transport Step Budget 20639.
Redirect "litarith_budget_bud_dvd_stop.log" Succeed Lean Import "../dumps/lean434/litarith.ndjson" 24796 24797.
Set Lean Transport Step Budget 20640.
Redirect "litarith_budget_bud_dvd_part.log" Succeed Lean Import "../dumps/lean434/litarith.ndjson" 24796 24797.
Set Lean Transport Step Budget 20641.
Redirect "litarith_budget_bud_dvd_over.log" Succeed Lean Import "../dumps/lean434/litarith.ndjson" 24796 24797.
Unset Lean Transport Step Budget.
Redirect "litarith_budget_bud_dvd.log" Lean Import "../dumps/lean434/litarith.ndjson" 24796 24797.

Set Lean Transport Step Budget 5585.
Redirect "litarith_budget_bud_hold_stop.log" Succeed Lean Import "../dumps/lean434/litarith.ndjson" 24804 24805.
Set Lean Transport Step Budget 5586.
Redirect "litarith_budget_bud_hold_part.log" Succeed Lean Import "../dumps/lean434/litarith.ndjson" 24804 24805.
Set Lean Transport Step Budget 5587.
Redirect "litarith_budget_bud_hold_over.log" Succeed Lean Import "../dumps/lean434/litarith.ndjson" 24804 24805.
Unset Lean Transport Step Budget.
Redirect "litarith_budget_bud_hold.log" Lean Import "../dumps/lean434/litarith.ndjson" 24804 24805.

Set Lean Transport Step Budget 192122.
Redirect "litarith_budget_bud_total_stop.log" Succeed Lean Import "../dumps/lean434/litarith.ndjson" 25339 25340.
Set Lean Transport Step Budget 192123.
Redirect "litarith_budget_bud_total_part.log" Succeed Lean Import "../dumps/lean434/litarith.ndjson" 25339 25340.
Unset Lean Transport Step Budget.
Redirect "litarith_budget_bud_total.log" Lean Import "../dumps/lean434/litarith.ndjson" 25339 25340.

Redirect "litarith_budget_loop_head.log" Lean Import "../dumps/lean434/litarith.ndjson" 25462 25463.
Redirect "litarith_budget_nested_cap.log" Lean Import "../dumps/lean434/litarith.ndjson" 25668 25669.
Redirect "litarith_budget_expo_share.log" Lean Import "../dumps/lean434/litarith.ndjson" 25865 25866.

Set Lean Transport Step Budget 200984.
Redirect "litarith_budget_order_pair.log" Succeed Lean Import "../dumps/lean434/litarith.ndjson" 25683 25684.
Unset Lean Transport Step Budget.

Redirect "litarith_budget_keep9.log" Lean Import "../dumps/lean434/litarith.ndjson" 25695 25696.
Set Lean Transport Step Budget 201327.
Redirect "litarith_budget_order_total.log" Succeed Lean Import "../dumps/lean434/litarith.ndjson" 25920 25921.
Unset Lean Transport Step Budget.

Redirect "litarith_budget_proof_size.log" Lean Import "../dumps/lean434/litarith.ndjson" 26146 26172.
Redirect "litarith_budget_nest_capped.log" Lean Import "../dumps/lean434/litarith.ndjson" 26172 26220.
