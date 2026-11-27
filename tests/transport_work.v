From LeanImport Require Import Lean.

(* Each limited setting is a measured debit of the importer, read from counters of this file compiled under its
   own name (one line per entry and budget: the debit of the entry's own part, of its largest argument part, and
   the total); a renamed copy whose Check lines were comments measured other debits. A budget-stop case is set
   one step below the larger of the two parts of the same entry at the default
   budget, so the pass stops at its last step and casts with one step more; a casting case with a limited
   setting is set at that larger part, so one step more stops it. The matching .expect asserts the budget stop
   separately from the kernel declaration result. Each replay rolls back its import. *)
Set Warnings "+unknown-option".
Set Lean Transport Step Budget 1000000.
Set Lean Entry Timeout 20.
Set Lean Error Mode "Skip".

(* W02: resolve the Nat instance of HAdd.hAdd in the presence of a lifted instance. *)
Redirect "transport_work_instances_deps.log" Lean Import "../dumps/lean434/transport_work.ndjson" 1 766.
Set Lean Transport Step Budget 160736.
Redirect "transport_work_instances_resolve.log" Succeed Lean Import "../dumps/lean434/transport_work.ndjson" 766 767.
Unset Lean Transport Step Budget.
Redirect "transport_work_instances.log" Lean Import "../dumps/lean434/transport_work.ndjson" 766 767.
Check RLI434W_instances.

(* W03a: an instantiated Nat body has a large raw term. *)
Redirect "transport_work_poly_nat_deps.log" Lean Import "../dumps/lean434/transport_work.ndjson" 767 883.
Set Lean Transport Step Budget 76435.
Redirect "transport_work_poly_nat_body.log" Succeed Lean Import "../dumps/lean434/transport_work.ndjson" 883 884.
Unset Lean Transport Step Budget.
Redirect "transport_work_poly_nat.log" Lean Import "../dumps/lean434/transport_work.ndjson" 883 884.
Check RLI434W_poly_nat.

(* W06a: search past both occupied generated names. *)
Redirect "transport_work_names_deps.log" Lean Import "../dumps/lean434/transport_work.ndjson" 884 900.
Definition RLI434W_names__nat_eq_1 : unit := tt.
Definition RLI434W_names__nat_eq_2 : unit := tt.
Set Lean Transport Step Budget 160114.
Redirect "transport_work_names_search.log" Succeed Lean Import "../dumps/lean434/transport_work.ndjson" 900 901.
Unset Lean Transport Step Budget.
Redirect "transport_work_names.log" Lean Import "../dumps/lean434/transport_work.ndjson" 900 901.
Check RLI434W_names.

(* W07: the new lemma must visit both endpoints, including the large sum. *)
Redirect "transport_work_endpoints_deps.log" Lean Import "../dumps/lean434/transport_work.ndjson" 901 907.
Set Lean Transport Step Budget 180914.
Redirect "transport_work_endpoints_endpoints.log" Succeed Lean Import "../dumps/lean434/transport_work.ndjson" 907 908.
Unset Lean Transport Step Budget.
Redirect "transport_work_endpoints.log" Lean Import "../dumps/lean434/transport_work.ndjson" 907 908.
Check RLI434W_endpoints.

(* W06b: a later entry reuses the checked endpoint lemma. *)
Redirect "transport_work_cache_hit_deps.log" Lean Import "../dumps/lean434/transport_work.ndjson" 908 909.
Redirect "transport_work_cache_hit.log" Lean Import "../dumps/lean434/transport_work.ndjson" 909 910.
Check RLI434W_cache_hit.

(* W06b: a miss also pays for all previously checked pairs. *)
Redirect "transport_work_cache_miss_deps.log" Lean Import "../dumps/lean434/transport_work.ndjson" 910 1017.
Set Lean Transport Step Budget 197823.
Redirect "transport_work_cache_miss_cache.log" Succeed Lean Import "../dumps/lean434/transport_work.ndjson" 1017 1018.
Unset Lean Transport Step Budget.
Redirect "transport_work_cache_miss.log" Lean Import "../dumps/lean434/transport_work.ndjson" 1017 1018.
Check RLI434W_cache_miss.

(* W09c: equal non-identical Nat terms do not get a lemma. Their comparison costs steps. *)
Redirect "transport_work_equal_nodes_deps.log" Lean Import "../dumps/lean434/transport_work.ndjson" 1018 1039.
Set Lean Transport Step Budget 271763.
Redirect "transport_work_equal_nodes_equality.log" Succeed Lean Import "../dumps/lean434/transport_work.ndjson" 1039 1040.
Unset Lean Transport Step Budget.
Redirect "transport_work_equal_nodes.log" Lean Import "../dumps/lean434/transport_work.ndjson" 1039 1040.
Check RLI434W_equal_nodes.

(* W12/W15/W26c: three distinct holes and one duplicate; keep lemma order and charge cumulative proof lift. The one
   stop case serves each of these charges: a pass that drops one of them casts there. *)
Redirect "transport_work_motives_deps.log" Lean Import "../dumps/lean434/transport_work.ndjson" 1040 8921.
Set Lean Transport Step Budget 316980.
Redirect "transport_work_motives_stop.log" Succeed Lean Import "../dumps/lean434/transport_work.ndjson" 8921 8922.
Unset Lean Transport Step Budget.
Redirect "transport_work_motives.log" Lean Import "../dumps/lean434/transport_work.ndjson" 8921 8922.
Check RLI434W_motives.

(* W16: the fitting dependent proof casts. Its argument part is larger than its own part, which W16's charges
   are in, so W16's stop case is on dependent_own below. *)
Redirect "transport_work_dependent_deps.log" Lean Import "../dumps/lean434/transport_work.ndjson" 8922 9015.
Redirect "transport_work_dependent.log" Lean Import "../dumps/lean434/transport_work.ndjson" 9015 9016.
Check RLI434W_dependent.

(* W18/W19a: a transparent product alias still exposes a proof binder (its stop case is on alias_own below). *)
Redirect "transport_work_alias_product_deps.log" Lean Import "../dumps/lean434/transport_work.ndjson" 9016 9031.
Redirect "transport_work_alias_product.log" Lean Import "../dumps/lean434/transport_work.ndjson" 9031 9032.
Check RLI434W_alias_product.

(* W18/W19a: decline a product behind a match; the original definition still checks. *)
Redirect "transport_work_computed_head_deps.log" Lean Import "../dumps/lean434/transport_work.ndjson" 9032 9216.
Redirect "transport_work_computed_head.log" Lean Import "../dumps/lean434/transport_work.ndjson" 9216 9217.
Check RLI434W_computed_head.

(* W19b: decline an unsupported computed type on the argument path. *)
Redirect "transport_work_computed_arg_deps.log" Lean Import "../dumps/lean434/transport_work.ndjson" 9217 9258.
Redirect "transport_work_computed_arg.log" Lean Import "../dumps/lean434/transport_work.ndjson" 9258 9259.
Check RLI434W_computed_arg.

(* W19b: actual proof typing reaches a match-hidden product and must decline. *)
Redirect "transport_work_computed_arg_product_deps.log" Lean Import "../dumps/lean434/transport_work.ndjson" 9259 9283.
Redirect "transport_work_computed_arg_product.log" Lean Import "../dumps/lean434/transport_work.ndjson" 9283 9284.
Check RLI434W_computed_arg_product.

(* W17/W19b: a typed argument casts after syntax-directed beta normalization. *)
Redirect "transport_work_beta_normalize_deps.log" Lean Import "../dumps/lean434/transport_work.ndjson" 9284 9292.
Set Lean Transport Step Budget 6287.
Redirect "transport_work_beta_normalize_normalize.log" Succeed Lean Import "../dumps/lean434/transport_work.ndjson" 9292 9293.
Unset Lean Transport Step Budget.
Redirect "transport_work_beta_normalize.log" Lean Import "../dumps/lean434/transport_work.ndjson" 9292 9293.
Check RLI434W_beta_normalize.

(* W20a: a cast under leading result binders (stop case on result_own below). *)
Redirect "transport_work_result_binders_deps.log" Lean Import "../dumps/lean434/transport_work.ndjson" 9293 9545.
Redirect "transport_work_result_binders.log" Lean Import "../dumps/lean434/transport_work.ndjson" 9545 9546.
Check RLI434W_result_binders.

(* W14a: the wide constructor type is read once (stop case on global_type_own below). *)
Redirect "transport_work_global_type_deps.log" Lean Import "../dumps/lean434/transport_work.ndjson" 9546 10044.
Redirect "transport_work_global_type.log" Lean Import "../dumps/lean434/transport_work.ndjson" 10044 10045.
Check RLI434W_global_type.

(* W20b: the optional query declines a match-hidden proof sort. *)
Redirect "transport_work_computed_sort_deps.log" Lean Import "../dumps/lean434/transport_work.ndjson" 10045 10087.
Redirect "transport_work_computed_sort.log" Lean Import "../dumps/lean434/transport_work.ndjson" 10087 10088.
Check RLI434W_computed_sort.

(* W24a: A then B then A, distinct tails under colliding binary Nat.add prefixes. *)
Redirect "transport_work_collision_aba_deps.log" Lean Import "../dumps/lean434/transport_work.ndjson" 10088 10184.
Redirect "transport_work_collision_aba.log" Lean Import "../dumps/lean434/transport_work.ndjson" 10184 10185.
Check RLI434W_collision_aba.

(* W24a: another entry starts with empty caches; exchange A and B. *)
Redirect "transport_work_collision_fresh_deps.log" Lean Import "../dumps/lean434/transport_work.ndjson" 10185 10213.
Redirect "transport_work_collision_fresh.log" Lean Import "../dumps/lean434/transport_work.ndjson" 10213 10214.
Check RLI434W_collision_fresh.

(* W24b: colliding suffixes with a finite budget for the direct-mapped cache. One step below the entry's largest
   part the pass stops (a pass without the get or the put charge casts there), and at that part it casts (a pass
   that pays more, as a chained table does, stops). *)
Redirect "transport_work_collision_chain_deps.log" Lean Import "../dumps/lean434/transport_work.ndjson" 10214 10421.
Set Lean Transport Step Budget 81119.
Redirect "transport_work_collision_chain_stop.log" Succeed Lean Import "../dumps/lean434/transport_work.ndjson" 10421 10422.
Unset Lean Transport Step Budget.
Set Lean Transport Step Budget 81120.
Redirect "transport_work_collision_chain.log" Lean Import "../dumps/lean434/transport_work.ndjson" 10421 10422.
Check RLI434W_collision_chain.
Unset Lean Transport Step Budget.

(* W25: omit type peels on Nat.succ, but visit the different unary head with a proof binder. N is the
   candidate's largest part (its argument part; its own part is smaller), below the own part of the measured
   mutant that reads the type of every Nat.succ. *)
Redirect "transport_work_nested_cast_deps.log" Lean Import "../dumps/lean434/transport_work.ndjson" 10422 11470.
Set Lean Transport Step Budget 5480.
Redirect "transport_work_nested_cast.log" Lean Import "../dumps/lean434/transport_work.ndjson" 11470 11471.
Check RLI434W_nested_cast.
Unset Lean Transport Step Budget.

(* W17/W26b: normalization creates a small shared term alongside the Fin hole. *)
Redirect "transport_work_normalize_fits_deps.log" Lean Import "../dumps/lean434/transport_work.ndjson" 11471 11546.
Set Lean Transport Step Budget 8376.
Redirect "transport_work_normalize_fits_shared_beta.log" Succeed Lean Import "../dumps/lean434/transport_work.ndjson" 11546 11547.
Unset Lean Transport Step Budget.
Redirect "transport_work_normalize_fits.log" Lean Import "../dumps/lean434/transport_work.ndjson" 11546 11547.
Check RLI434W_normalize_fits.

(* Stops on the entry's own part (rows W02's instance collection, W14a, W16, W18/W19a and W20a, whose charges
   are in that part). In each entry below (the last five of dumps/lean434/src/RLI434Work.lean) a hypothesis
   over a ballast term, which only the entry's own scan and walk read, makes the entry's own part its largest
   part; a stop case is set one step below that part, so a pass that drops one of those charges casts there.
   Each Fin hole compares UInt8 values, which the kernel converts at once after a stop. The casting import of
   each entry runs under Succeed too, so that no lemma or declaration of these entries is left for the cases
   after them; its log line, written once the kernel has accepted the transported value, is the check. The
   own parts, from the counters of this file at every part's default budget:
   instances_own 25,448, global_type_own 27,041, dependent_own 25,085, alias_own 24,995, result_own 25,272; no
   argument part of these entries was above 5,948 there. *)

(* W02: the entry's view collects HAdd.hAdd, which the export has at two universes; the Fin value 4 + 3 reads
   it at Nat's instance. *)
Redirect "transport_work_instances_own_deps.log" Lean Import "../dumps/lean434/transport_work.ndjson" 11771 11823.
Set Lean Transport Step Budget 25447.
Redirect "transport_work_instances_own_collect.log" Succeed Lean Import "../dumps/lean434/transport_work.ndjson" 11823 11824.
Unset Lean Transport Step Budget.
Redirect "transport_work_instances_own.log" Succeed Lean Import "../dumps/lean434/transport_work.ndjson" 11823 11824.

(* W14a: the first scan reads the long declared type of the constructor Wide.mk. *)
Redirect "transport_work_global_type_own_deps.log" Lean Import "../dumps/lean434/transport_work.ndjson" 11824 11839.
Set Lean Transport Step Budget 27040.
Redirect "transport_work_global_type_own_constructor.log" Succeed Lean Import "../dumps/lean434/transport_work.ndjson" 11839 11840.
Unset Lean Transport Step Budget.
Redirect "transport_work_global_type_own.log" Succeed Lean Import "../dumps/lean434/transport_work.ndjson" 11839 11840.

(* W16: a dependent domain, a codomain exposed after the substitution of the arguments before it, and the
   first copy of the argument array; the one stop case serves each of these charges. *)
Redirect "transport_work_dependent_own_deps.log" Lean Import "../dumps/lean434/transport_work.ndjson" 11840 11875.
Set Lean Transport Step Budget 25084.
Redirect "transport_work_dependent_own_stop.log" Succeed Lean Import "../dumps/lean434/transport_work.ndjson" 11875 11876.
Unset Lean Transport Step Budget.
Redirect "transport_work_dependent_own.log" Succeed Lean Import "../dumps/lean434/transport_work.ndjson" 11875 11876.

(* W18/W19a: the head's type is read and its product exposed through the alias Dep8; the one stop case serves
   the product exposure (W18) and the head's type read (W19a). *)
Redirect "transport_work_alias_own_deps.log" Lean Import "../dumps/lean434/transport_work.ndjson" 11876 11891.
Set Lean Transport Step Budget 24994.
Redirect "transport_work_alias_own_stop.log" Succeed Lean Import "../dumps/lean434/transport_work.ndjson" 11891 11892.
Unset Lean Transport Step Budget.
Redirect "transport_work_alias_own.log" Succeed Lean Import "../dumps/lean434/transport_work.ndjson" 11891 11892.

(* W20a: the result walk descends 80 leading binders to the proof it casts. *)
Redirect "transport_work_result_own_deps.log" Lean Import "../dumps/lean434/transport_work.ndjson" 11892 11982.
Set Lean Transport Step Budget 25271.
Redirect "transport_work_result_own_result.log" Succeed Lean Import "../dumps/lean434/transport_work.ndjson" 11982 11983.
Unset Lean Transport Step Budget.
Redirect "transport_work_result_own.log" Succeed Lean Import "../dumps/lean434/transport_work.ndjson" 11982 11983.

(* W26b: the input fits; beta substitution creates sharing whose expanded work must not wrap. *)
Redirect "transport_work_normalize_overflow_deps.log" Lean Import "../dumps/lean434/transport_work.ndjson" 11547 11594.
Set Lean Transport Step Budget 4611686018427387903.
Redirect "transport_work_normalize_overflow.log" Lean Import "../dumps/lean434/transport_work.ndjson" 11594 11595.
Check RLI434W_normalize_overflow.
Unset Lean Transport Step Budget.

(* W11: an occupied physical slot returns the value of the same nonconstant Nat.add. *)
Redirect "transport_work_shared_some_deps.log" Lean Import "../dumps/lean434/transport_work.ndjson" 11595 11732.
Set Lean Transport Step Budget 10319.
Redirect "transport_work_shared_some.log" Lean Import "../dumps/lean434/transport_work.ndjson" 11732 11733.
Check RLI434W_shared_some.
Unset Lean Transport Step Budget.

(* W11: an occupied physical slot records absence for the same nonconstant Nat.sub. *)
Redirect "transport_work_shared_none_deps.log" Lean Import "../dumps/lean434/transport_work.ndjson" 11733 11770.
Set Lean Transport Step Budget 13527.
Redirect "transport_work_shared_none.log" Lean Import "../dumps/lean434/transport_work.ndjson" 11770 11771.
Check RLI434W_shared_none.
Unset Lean Transport Step Budget.
