From LeanImport Require Import Lean.

(* The kernel refuses a value with relevant casts (README, "Transport of proof arguments across Nat literals", the
   item on relevant positions). dumps/lean434/relcast_refused.ndjson is dumps/lean434/relcast.ndjson with the
   library's Nat.mod renamed Nat.modLib and the fixtures' RLI434RC.pmod named Nat.mod, its value fun _ _ => 0 (its
   row in dumps/lean434/README.md); it is the only export of this document, since the pass's lists of the export's
   constants of a name are document-wide. It imports the library (lines 1 to 15433), then:
   - refused_mod (line 16254): its first relevant argument's Fin value goes through the planted Nat.mod, so its
     lemma RLI434RC_refused_mod__rel_eq_1 is refused; its second is cast along RLI434RC_refused_mod__rel_eq_2. The
     kernel refuses that value, whose first argument stays ill-typed, and then Lean's value; the entry is refused,
     and the lemma it declared goes with it.
   - refused_mod_sprop (line 16283): the same with a proof cast of the SProp pass: the relevant pass's value,
     then the SProp pass's value, then Lean's value are refused, in that order.
   - refused_255, refused_256, refused_257 (lines 16318, 16325, 16331): a small value
     the kernel refuses (a proof of pmod 3 8 = 3, after the plant), beside one relevant cast; the kernel's error is
     printed for a refused value of at most 256 nodes.
   - after_refused (line 16333): the pair of refused_mod's second argument, which declares a lemma of its own:
     the refused entry's lemma left the relevant pass's cache with it.
   tests/relcast_refused.expect checks the logs. *)
Set Warnings "+unknown-option".
Set Lean Error Mode "Skip".
Set Lean Entry Timeout 10.
Redirect "relcast_refused_lib.log" Lean Import "../dumps/lean434/relcast_refused.ndjson" 1 15434.
Redirect "relcast_refused_mod.log" Lean Import "../dumps/lean434/relcast_refused.ndjson" 16232 16255.
Redirect "relcast_refused_mod_sprop.log" Lean Import "../dumps/lean434/relcast_refused.ndjson" 16255 16284.
Redirect "relcast_refused_255.log" Lean Import "../dumps/lean434/relcast_refused.ndjson" 16284 16319.
Redirect "relcast_refused_256.log" Lean Import "../dumps/lean434/relcast_refused.ndjson" 16319 16326.
Redirect "relcast_refused_257.log" Lean Import "../dumps/lean434/relcast_refused.ndjson" 16326 16332.
Redirect "relcast_after_refused.log" Lean Import "../dumps/lean434/relcast_refused.ndjson" 16332 16334.

(* F-cache-later: theorem_closed, rel_total_hi discarded by its total, then cache_after at the head's part. *)
Redirect "relcast_refused_theorem.log" Lean Import "../dumps/lean434/relcast_refused.ndjson" 15434 15435.
Set Lean Transport Step Budget 150000.
Redirect "relcast_refused_total.log" Lean Import "../dumps/lean434/relcast_refused.ndjson" 16169 16170.
Unset Lean Transport Step Budget.
Set Lean Transport Step Budget 104707.
Redirect "relcast_refused_cache_head.log" Succeed Lean Import "../dumps/lean434/relcast_refused.ndjson" 16212 16213.
Unset Lean Transport Step Budget.
Redirect "relcast_refused_cache.log" Lean Import "../dumps/lean434/relcast_refused.ndjson" 16212 16213.

Fail Check RLI434RC_refused_mod.
Fail Check RLI434RC_refused_mod__rel_eq_1.
Fail Check RLI434RC_refused_mod__rel_eq_2.
Fail Check RLI434RC_refused_mod_sprop.
Check RLI434RC_after_refused.
Check RLI434RC_after_refused__rel_eq_1.
Check RLI434RC_theorem_closed.
Check RLI434RC_rel_total_hi.
Check RLI434RC_rel_total_hi__rel_eq_1.
Check RLI434RC_cache_after.
Redirect "relcast_refused_pa_after.log" Print Assumptions RLI434RC_after_refused.
