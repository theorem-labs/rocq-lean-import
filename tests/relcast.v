From LeanImport Require Import Lean.

(* A cast at a relevant position (README, "Transport of proof arguments across Nat literals", the item on relevant
   positions). dumps/lean434/relcast.ndjson is exported from dumps/lean434/src/RLI434RelCast.lean (its row in
   dumps/lean434/README.md).
   - theorem_closed (line 15434): a theorem whose value holds, once, ite (c.val <= 65535) with the instance
     UInt32.decLe c.val (UInt32.ofNatLT 65535 _), where ite expects Decidable (c.val <= (65535 : UInt32)); no SProp
     argument differs. The pass casts the instance along RLI434RC_theorem_closed__rel_eq_1, and the kernel accepts
     the value. The src/ of the fix's parent casts nothing, and the kernel's conversion of the instance outlasts the
     10 s limit below.
   - again (line 15436): the same closed pair; its cast reuses theorem_closed's lemma.
   - data_closed (line 15440): Char -> Nat with the same ite, a data definition: no cast on either side, and the
     kernel's conversion outlasts the limit.
   - head_stop_hit (line 15504), near the end at the step budget 2700: the SProp pass stops, so no relevant
     pass runs and Lean's value goes to the kernel.
   - The declared types of theorem_closed and declared_B (the kernel checks a candidate at Lean's type), of the axiom
     kind_axiom and of the inductive KindInd (no value, so the pass never sees them) are printed and pinned.
   One planted check is not in this suite: a candidate replaced by a term of the wrong type needs a patched plugin,
   so it runs only in a Job (the kernel refuses it; the SProp pass's value, else Lean's, goes to the kernel).
   tests/relcast_depth.v checks the nesting limit 10000 of the detector and of the relevant pass.
   tests/relcast.expect checks the logs. *)
Set Warnings "+unknown-option".
Set Lean Error Mode "Skip".
Set Lean Entry Timeout 10.
Redirect "relcast_lib.log" Lean Import "../dumps/lean434/relcast.ndjson" 1 15434.

Redirect "relcast_theorem.log" Lean Import "../dumps/lean434/relcast.ndjson" 15434 15435.
Redirect "relcast_again.log" Lean Import "../dumps/lean434/relcast.ndjson" 15435 15437.
Redirect "relcast_data.log" Lean Import "../dumps/lean434/relcast.ndjson" 15437 15441.

(* One Redirect per case, in the export's order (dumps/lean434/README.md
   names each entry): an accepted line with relevant casts where the pass casts; no line where it casts nothing
   and the kernel converts the pair at once; the 10 s limit where it casts nothing and the kernel computes the
   65535 pair on the unary Nat. *)
Redirect "relcast_aux_closed.log" Lean Import "../dumps/lean434/relcast.ndjson" 15441 15443.
Redirect "relcast_aux_user.log" Lean Import "../dumps/lean434/relcast.ndjson" 15443 15448.
Redirect "relcast_reverse_closed.log" Lean Import "../dumps/lean434/relcast.ndjson" 15448 15457.
Redirect "relcast_keep_sprop.log" Lean Import "../dumps/lean434/relcast.ndjson" 15457 15488.
Redirect "relcast_body_type.log" Lean Import "../dumps/lean434/relcast.ndjson" 15505 15517.
Redirect "relcast_beta_visible.log" Lean Import "../dumps/lean434/relcast.ndjson" 15517 15527.
Redirect "relcast_beta_only.log" Lean Import "../dumps/lean434/relcast.ndjson" 15527 15538.
Redirect "relcast_beta_erased.log" Lean Import "../dumps/lean434/relcast.ndjson" 15538 15558.
Redirect "relcast_bare_domain.log" Lean Import "../dumps/lean434/relcast.ndjson" 15558 15567.
Redirect "relcast_no_fin.log" Lean Import "../dumps/lean434/relcast.ndjson" 15567 15582.
Redirect "relcast_literal_only.log" Lean Import "../dumps/lean434/relcast.ndjson" 15582 15593.
Redirect "relcast_over_double.log" Lean Import "../dumps/lean434/relcast.ndjson" 15593 15607.
Redirect "relcast_ofnat_2047.log" Lean Import "../dumps/lean434/relcast.ndjson" 15607 15614.
Redirect "relcast_ofnat_65535.log" Lean Import "../dumps/lean434/relcast.ndjson" 15614 15617.
Redirect "relcast_under_succ.log" Lean Import "../dumps/lean434/relcast.ndjson" 15617 15632.
Redirect "relcast_domain_product.log" Lean Import "../dumps/lean434/relcast.ndjson" 15632 15644.
Redirect "relcast_domain_var.log" Lean Import "../dumps/lean434/relcast.ndjson" 15644 15654.
Redirect "relcast_domain_alias.log" Lean Import "../dumps/lean434/relcast.ndjson" 15654 15661.
Redirect "relcast_opaque_fun_type.log" Lean Import "../dumps/lean434/relcast.ndjson" 15661 15668.
Redirect "relcast_unreadable_argument.log" Lean Import "../dumps/lean434/relcast.ndjson" 15668 15677.
Redirect "relcast_unreadable_prop_sort.log" Lean Import "../dumps/lean434/relcast.ndjson" 15677 15681.
Redirect "relcast_prop_alias.log" Lean Import "../dumps/lean434/relcast.ndjson" 15681 15685.
Redirect "relcast_data_alias.log" Lean Import "../dumps/lean434/relcast.ndjson" 15685 15689.
Redirect "relcast_open_actual.log" Lean Import "../dumps/lean434/relcast.ndjson" 15689 15701.
Redirect "relcast_open_expected.log" Lean Import "../dumps/lean434/relcast.ndjson" 15701 15712.
Redirect "relcast_same_instance.log" Lean Import "../dumps/lean434/relcast.ndjson" 15712 15719.
Redirect "relcast_same_head.log" Lean Import "../dumps/lean434/relcast.ndjson" 15719 15730.
Redirect "relcast_not_fin.log" Lean Import "../dumps/lean434/relcast.ndjson" 15730 15756.
Redirect "relcast_nat_only.log" Lean Import "../dumps/lean434/relcast.ndjson" 15756 15776.
Redirect "relcast_mixed_holes.log" Lean Import "../dumps/lean434/relcast.ndjson" 15776 15786.
Redirect "relcast_fin_65536.log" Lean Import "../dumps/lean434/relcast.ndjson" 15786 15802.
Redirect "relcast_fin_65537.log" Lean Import "../dumps/lean434/relcast.ndjson" 15802 15818.
Redirect "relcast_h_pair.log" Lean Import "../dumps/lean434/relcast.ndjson" 15818 15825.
Redirect "relcast_relhole_reverse.log" Lean Import "../dumps/lean434/relcast.ndjson" 15825 15840.
Redirect "relcast_relhole_no_fin.log" Lean Import "../dumps/lean434/relcast.ndjson" 15840 15853.
Redirect "relcast_declared_B.log" Lean Import "../dumps/lean434/relcast.ndjson" 15853 15857.
Redirect "relcast_no_trigger.log" Lean Import "../dumps/lean434/relcast.ndjson" 15857 15863.
Redirect "relcast_higher_domain.log" Lean Import "../dumps/lean434/relcast.ndjson" 15863 15878.
Redirect "relcast_universe_max.log" Lean Import "../dumps/lean434/relcast.ndjson" 15878 15892.
Redirect "relcast_lemma_absent.log" Lean Import "../dumps/lean434/relcast.ndjson" 15892 15918.
Redirect "relcast_two_holes_one_absent.log" Lean Import "../dumps/lean434/relcast.ndjson" 15918 15934.
Redirect "relcast_candidate_limit.log" Lean Import "../dumps/lean434/relcast.ndjson" 15934 15946.

(* B-overflow: the budget around max_int / 10, where ten times the budget saturates at max_int. *)
Set Lean Transport Step Budget 461168601842738789.
Redirect "relcast_cap_mul_lo.log" Succeed Lean Import "../dumps/lean434/relcast.ndjson" 15947 15948.
Set Lean Transport Step Budget 461168601842738790.
Redirect "relcast_cap_mul_at.log" Succeed Lean Import "../dumps/lean434/relcast.ndjson" 15947 15948.
Set Lean Transport Step Budget 461168601842738791.
Redirect "relcast_cap_mul_hi.log" Succeed Lean Import "../dumps/lean434/relcast.ndjson" 15947 15948.
Unset Lean Transport Step Budget.

(* The budget fixtures: B-arg (rel_arg), B-own (rel_own), B-detect-part (detect_arg) at budgets around the
   part the default-budget import measures; F-cache-later (rel_total_hi discarded, then cache_after). *)
Set Lean Transport Step Budget 107302.
Redirect "relcast_rel_arg_lo.log" Succeed Lean Import "../dumps/lean434/relcast.ndjson" 15983 15984.
Set Lean Transport Step Budget 107301.
Redirect "relcast_rel_arg_at.log" Succeed Lean Import "../dumps/lean434/relcast.ndjson" 15983 15984.
Set Lean Transport Step Budget 107300.
Redirect "relcast_rel_arg_hi.log" Succeed Lean Import "../dumps/lean434/relcast.ndjson" 15983 15984.
Unset Lean Transport Step Budget.
Redirect "relcast_rel_arg.log" Lean Import "../dumps/lean434/relcast.ndjson" 15983 15984.
Redirect "relcast_rel_own_lib.log" Lean Import "../dumps/lean434/relcast.ndjson" 15995 15996.
Set Lean Transport Step Budget 9537.
Redirect "relcast_rel_own_lo.log" Succeed Lean Import "../dumps/lean434/relcast.ndjson" 16128 16129.
Set Lean Transport Step Budget 9536.
Redirect "relcast_rel_own_at.log" Succeed Lean Import "../dumps/lean434/relcast.ndjson" 16128 16129.
Set Lean Transport Step Budget 9535.
Redirect "relcast_rel_own_hi.log" Succeed Lean Import "../dumps/lean434/relcast.ndjson" 16128 16129.
Unset Lean Transport Step Budget.
Redirect "relcast_rel_own.log" Lean Import "../dumps/lean434/relcast.ndjson" 16128 16129.
Set Lean Transport Step Budget 150000.
Redirect "relcast_rel_total_hi.log" Lean Import "../dumps/lean434/relcast.ndjson" 16169 16170.
Unset Lean Transport Step Budget.
Set Lean Transport Step Budget 6400.
Redirect "relcast_detect_arg_lo.log" Succeed Lean Import "../dumps/lean434/relcast.ndjson" 16179 16180.
Set Lean Transport Step Budget 6399.
Redirect "relcast_detect_arg_at.log" Succeed Lean Import "../dumps/lean434/relcast.ndjson" 16179 16180.
Set Lean Transport Step Budget 6398.
Redirect "relcast_detect_arg_hi.log" Succeed Lean Import "../dumps/lean434/relcast.ndjson" 16179 16180.
Unset Lean Transport Step Budget.
Redirect "relcast_detect_arg.log" Lean Import "../dumps/lean434/relcast.ndjson" 16179 16180.
Redirect "relcast_detect_total_hi.log" Lean Import "../dumps/lean434/relcast.ndjson" 16199 16200.
Redirect "relcast_cache_after.log" Lean Import "../dumps/lean434/relcast.ndjson" 16212 16213.

(* V-mismatch: a record parameter and a Fin bound the parameter reader cannot read, a Fin value the Fin
   case's reader cannot read, each beside its control, which is cast. *)
Redirect "relcast_param_mismatch.log" Lean Import "../dumps/lean434/relcast.ndjson" 16334 16486.
Redirect "relcast_param_match.log" Lean Import "../dumps/lean434/relcast.ndjson" 16486 16512.
Redirect "relcast_bound_mismatch.log" Lean Import "../dumps/lean434/relcast.ndjson" 16512 16631.
Redirect "relcast_bound_match.log" Lean Import "../dumps/lean434/relcast.ndjson" 16631 16647.
Redirect "relcast_opaque_value.log" Lean Import "../dumps/lean434/relcast.ndjson" 16647 16692.
Redirect "relcast_readable_value.log" Lean Import "../dumps/lean434/relcast.ndjson" 16692 16720.

(* E-sort-other: sortpoly.{u}'s type has the sort u; both instances declared: RLI434RC_sortpoly (u a level,
   a data definition: no relevant pass, its value Lean's) and RLI434RC_sortpoly_inst1 (u := SProp, a
   proposition: the cast, the line). *)
Set Lean Upfront Instantiation.
Redirect "relcast_sortpoly.log" Lean Import "../dumps/lean434/relcast.ndjson" 16720 16733.
Unset Lean Upfront Instantiation.
Redirect "relcast_sortpoly_data.log" Print RLI434RC_sortpoly.
Redirect "relcast_sortpoly_prop.log" Print RLI434RC_sortpoly_inst1.

(* V-mismatch, record chains: ign ignores its arguments, so the pair at their second arguments is of two
   records (record_mismatch); the control has the W pair there. *)
Redirect "relcast_record_mismatch.log" Lean Import "../dumps/lean434/relcast.ndjson" 16733 16762.
Redirect "relcast_record_match.log" Lean Import "../dumps/lean434/relcast.ndjson" 16762 16776.

(* B-stop: head_stop_hit at the budget 2700, where the detector finds its early site (2601 steps) and the
   SProp pass's later cast needs more (2935): the SProp pass stops, no relevant pass runs, and Lean's value
   outlasts the limit, as at the head. *)
Set Lean Transport Step Budget 2700.
Redirect "relcast_head_stop.log" Succeed Lean Import "../dumps/lean434/relcast.ndjson" 15504 15505.
Unset Lean Transport Step Budget.

Redirect "relcast_type_theorem_closed.log" Check RLI434RC_theorem_closed.
Check RLI434RC_again.
Fail Check RLI434RC_data_closed.
Check RLI434RC_aux_closed.
Check RLI434RC_aux_user.
Check RLI434RC_reverse_closed.
Check RLI434RC_keep_sprop.
Check RLI434RC_body_type.
Check RLI434RC_beta_visible.
Check RLI434RC_beta_erased.
Check RLI434RC_bare_domain.
Check RLI434RC_no_fin.
Check RLI434RC_literal_only.
Check RLI434RC_over_double.
Check RLI434RC_ofnat_2047.
Check RLI434RC_ofnat_65535.
Check RLI434RC_prop_alias.
Check RLI434RC_same_instance.
Check RLI434RC_same_head.
Check RLI434RC_not_fin.
Check RLI434RC_h_pair.
Check RLI434RC_relhole_reverse.
Check RLI434RC_relhole_no_fin.
Redirect "relcast_type_declared_B.log" Check RLI434RC_declared_B.
Check RLI434RC_no_trigger.
Check RLI434RC_higher_domain.
Check RLI434RC_universe_max.
Check RLI434RC_lemma_absent.
Check RLI434RC_two_holes_one_absent.
Check RLI434RC_rel_arg.
Check RLI434RC_rel_own_lib.
Check RLI434RC_rel_own.
Check RLI434RC_rel_total_hi.
Check RLI434RC_detect_arg.
Check RLI434RC_detect_total_hi.
Check RLI434RC_cache_after.
Check RLI434RC_param_mismatch.
Check RLI434RC_param_match.
Check RLI434RC_bound_mismatch.
Check RLI434RC_bound_match.
Check RLI434RC_opaque_value.
Check RLI434RC_readable_value.
Check RLI434RC_record_mismatch.
Check RLI434RC_record_match.
Redirect "relcast_type_kind_axiom.log" Check RLI434RC_kind_axiom.
Redirect "relcast_type_KindInd.log" Print RLI434RC_KindInd.
Redirect "relcast_pa_theorem.log" Print Assumptions RLI434RC_theorem_closed.
Redirect "relcast_pa_again.log" Print Assumptions RLI434RC_again.
Redirect "relcast_pa_aux_closed.log" Print Assumptions RLI434RC_aux_closed.
Redirect "relcast_pa_aux_user.log" Print Assumptions RLI434RC_aux_user.
Redirect "relcast_pa_reverse_closed.log" Print Assumptions RLI434RC_reverse_closed.
Redirect "relcast_pa_keep_sprop.log" Print Assumptions RLI434RC_keep_sprop.
Redirect "relcast_pa_body_type.log" Print Assumptions RLI434RC_body_type.
Redirect "relcast_pa_beta_visible.log" Print Assumptions RLI434RC_beta_visible.
Redirect "relcast_pa_beta_erased.log" Print Assumptions RLI434RC_beta_erased.
Redirect "relcast_pa_bare_domain.log" Print Assumptions RLI434RC_bare_domain.
Redirect "relcast_pa_no_fin.log" Print Assumptions RLI434RC_no_fin.
Redirect "relcast_pa_literal_only.log" Print Assumptions RLI434RC_literal_only.
Redirect "relcast_pa_over_double.log" Print Assumptions RLI434RC_over_double.
Redirect "relcast_pa_ofnat_2047.log" Print Assumptions RLI434RC_ofnat_2047.
Redirect "relcast_pa_ofnat_65535.log" Print Assumptions RLI434RC_ofnat_65535.
Redirect "relcast_pa_prop_alias.log" Print Assumptions RLI434RC_prop_alias.
Redirect "relcast_pa_same_instance.log" Print Assumptions RLI434RC_same_instance.
Redirect "relcast_pa_same_head.log" Print Assumptions RLI434RC_same_head.
Redirect "relcast_pa_not_fin.log" Print Assumptions RLI434RC_not_fin.
Redirect "relcast_pa_h_pair.log" Print Assumptions RLI434RC_h_pair.
Redirect "relcast_pa_relhole_reverse.log" Print Assumptions RLI434RC_relhole_reverse.
Redirect "relcast_pa_relhole_no_fin.log" Print Assumptions RLI434RC_relhole_no_fin.
Redirect "relcast_pa_declared_B.log" Print Assumptions RLI434RC_declared_B.
Redirect "relcast_pa_no_trigger.log" Print Assumptions RLI434RC_no_trigger.
Redirect "relcast_pa_higher_domain.log" Print Assumptions RLI434RC_higher_domain.
Redirect "relcast_pa_universe_max.log" Print Assumptions RLI434RC_universe_max.
Redirect "relcast_pa_lemma_absent.log" Print Assumptions RLI434RC_lemma_absent.
Redirect "relcast_pa_two_holes_one_absent.log" Print Assumptions RLI434RC_two_holes_one_absent.
Redirect "relcast_pa_rel_arg.log" Print Assumptions RLI434RC_rel_arg.
Redirect "relcast_pa_rel_own_lib.log" Print Assumptions RLI434RC_rel_own_lib.
Redirect "relcast_pa_rel_own.log" Print Assumptions RLI434RC_rel_own.
Redirect "relcast_pa_rel_total_hi.log" Print Assumptions RLI434RC_rel_total_hi.
Redirect "relcast_pa_detect_arg.log" Print Assumptions RLI434RC_detect_arg.
Redirect "relcast_pa_detect_total_hi.log" Print Assumptions RLI434RC_detect_total_hi.
Redirect "relcast_pa_cache_after.log" Print Assumptions RLI434RC_cache_after.
Redirect "relcast_pa_param_mismatch.log" Print Assumptions RLI434RC_param_mismatch.
Redirect "relcast_pa_param_match.log" Print Assumptions RLI434RC_param_match.
Redirect "relcast_pa_bound_mismatch.log" Print Assumptions RLI434RC_bound_mismatch.
Redirect "relcast_pa_bound_match.log" Print Assumptions RLI434RC_bound_match.
Redirect "relcast_pa_opaque_value.log" Print Assumptions RLI434RC_opaque_value.
Redirect "relcast_pa_readable_value.log" Print Assumptions RLI434RC_readable_value.
Redirect "relcast_pa_record_mismatch.log" Print Assumptions RLI434RC_record_mismatch.
Redirect "relcast_pa_record_match.log" Print Assumptions RLI434RC_record_match.
