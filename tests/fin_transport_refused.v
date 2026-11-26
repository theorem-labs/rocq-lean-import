From LeanImport Require Import Lean.

(* The refusal path of the transport pass (README, "Transport of proof arguments across Nat literals"): a Fin
   hole and, in the same argument, a second difference that the pass leaves to the kernel and the kernel does not
   convert. dumps/lean434/fin_refused.ndjson is dumps/lean434/utf8size_two.ndjson without its last entry, with one
   theorem added (export line 11828):
     RLI434Fin.c6_127 : forall v : UInt32, (v <= UInt32.ofNatLT 127 _ /\ True) -> (v <= (127 : UInt32) /\ False)
     := fun v h => h.
   The pass casts h at the Fin hole (UInt32.ofNatLT 127 _ against 127) and leaves True against False to the
   kernel, which refuses the transported value. The importer logs that refusal, then gives Lean's own value to the
   kernel, which refuses it too: the entry is refused with Lean's error, and the lemma the pass declared for it is
   undone with it. The src/ of the fix's parent has no Fin case and logs no refusal of a transported value
   (ci/build-9.2-cut.sh --revert-fix). tests/fin_transport_refused.expect checks the log. *)
Set Warnings "+unknown-option".
Set Lean Entry Timeout 120.
Set Lean Error Mode "Skip".
Redirect "fin_transport_refused.log" Lean Import "../dumps/lean434/fin_refused.ndjson".

Fail Check RLI434Fin_c6_127__nat_eq_1.
Fail Check RLI434Fin_c6_127.
(* W21: the fallback retains Lean's error, and Skip continues. *)
Check RLI434Fin_after_refusal.
