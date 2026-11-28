From LeanImport Require Import Lean.

(* The cast at a relevant position (README, "Transport of proof arguments across Nat literals") goes through
   rel_transport of src/Lean.v, which relies on the definitional UIP of Lean's eq and on nothing else, as
   sprop_transport does (tests/nat_transport.v). The command is in a file of its own because the src/ of the fix's
   parent has no rel_transport, and tests/relcast.v is the file whose first entry error decides the control of
   ci/build-9.2-cut.sh --revert-fix. tests/relcast_lemma.expect checks the log. *)
Redirect "relcast_lemma_assumptions.log" Print Assumptions rel_transport.
