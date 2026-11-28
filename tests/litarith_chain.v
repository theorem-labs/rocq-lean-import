From LeanImport Require Import Lean.

(* Literal arithmetic, a chain of waits (README, "Transport of proof arguments across Nat literals"): a match, a
   fixpoint applied past its recursive index or a projection whose scrutinee, recursive argument or subject is
   itself one of these that waits on a held operation waits on it too, and contracts in the round after the held
   operation is replaced. This test is the per-fix control of that rule: one entry, imported alone after the
   definitions, so that its row is red on the src/ of the fix's parent and nothing else of the rule's tests is
   needed to see it. dumps/lean434/litarith.ndjson: the definitions (lines 1 to 23878), then chain_1 (line 26488)
   alone; its names and expressions are lines the parser reads before the range, and none of them is a theorem.
   - chain_1 (26488): -(4096 * 117349959766017) + 1 against -480665435201605631 at Int, the shape of the assemble
     roots' arithmetic (the importer writes 4096 unary, below 5000): Int.add's match on Int.negOfNat's fixpoint,
     which waits on the held 4096 * 117349959766017 (one link), in two replacement rounds; the pair's lemma is cast.
     The test's own entry, which the src/ of the fix's parent leaves to the kernel: the kernel's check of Lean's
     value does not end (a stack overflow after 9.4 s in the Job that measured it), and the entry is skipped.
   tests/litarith_chain.expect checks the logs. *)
Set Warnings "+unknown-option".
Set Lean Error Mode "Skip".
Set Lean Entry Timeout 10.
Redirect "litarith_chain_lib.log" Lean Import "../dumps/lean434/litarith.ndjson" 1 23879.
Redirect "litarith_chain.log" Lean Import "../dumps/lean434/litarith.ndjson" 26488 26489.

(* The lemma the cast uses exists; a lemma the kernel refused was not declared. *)
Check RLI434L_chain_1__nat_eq_4.
