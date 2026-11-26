From LeanImport Require Import Lean.

(* A nest of projections on both sides of a Fin pair (idA N against idB N; README, "Transport of proof arguments
   across Nat literals"):
   a projection's step is counted before its subject is reduced, so a nest deeper than the 64 steps a side may
   take stops there; that pair gets no lemma, and the entry's other arguments are still cast.
   dumps/lean434/fin_nest.ndjson is dumps/lean434/nest.ndjson (exported from dumps/lean434/src/RLI434Nest.lean)
   with a planted nest of 1000 projections (its row in dumps/lean434/README.md): N is 1000 projections of the
   axiom RLI434N.deep, RLI434N.axNest v : v <= RLI434N.idA N, and (export line 10564)
     RLI434N.nest_1000 : forall v : UInt32, v <= UInt32.ofNatLT 127 _ -> v <= 127 /\ v <= RLI434N.idB N
       := fun v h => And.intro _ _ h (RLI434N.axNest v).
   The pass casts h along RLI434N_nest_1000__nat_eq_1 and finds no Fin pair in idA N against idB N; the kernel
   converts that argument at once. On the Rocq 9.2 cut the entry's own part takes 9,078 steps and that argument
   25,224, its largest part; a pass that followed the nest to its end (no step reserved for a projection before
   its subject) would take 26,162 for it. At the budget below, 25,224, such a pass would stop for the whole entry,
   and its cast of h would be lost (the kernel then takes far longer than the 10 s limit). The budget
   applies to this entry only: the lines before it import at the default, but for RLI434N.cast_127 (export line
   8503), which is read and not imported. On an importer without the option the Set line only warns, and the
   entry is refused (no cast at all).
   tests/fin_transport_nest.expect checks the logs. *)
Set Lean Error Mode "Skip".
Set Lean Entry Timeout 10.
Redirect "fin_transport_nest_base.log" Lean Import "../dumps/lean434/fin_nest.ndjson" 1 8503.
Redirect "fin_transport_nest_rest.log" Lean Import "../dumps/lean434/fin_nest.ndjson" 8504 10564.

Set Lean Transport Step Budget 25224.
Redirect "fin_transport_nest.log" Lean Import "../dumps/lean434/fin_nest.ndjson" 10564.

Check RLI434N_nest_1000.
Redirect "fin_transport_nest_budget.log" Test Lean Transport Step Budget.
