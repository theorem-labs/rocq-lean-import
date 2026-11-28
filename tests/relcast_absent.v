From LeanImport Require Import Lean.

(* Without rel_transport (README, "Transport of proof arguments across Nat literals", the item on relevant
   positions): lean.rel_transport is bound to an inductive type, Lean's eq, so it names no constant and the relevant
   path is off; each entry's log is the one the pass gives without it. The registration is document-wide, so this
   test is a document of its own. dumps/lean434/relcast.ndjson is relcast.v's export:
   - theorem_closed (line 15434): no cast, and the kernel's conversion of its pair outlasts the 10 s limit;
   - h_pair (line 15824): its proof cast, whose motive holds Lean's instance at a place where the instance's type
     does not fit, is refused, and then Lean's value outlasts the limit;
   - rel_arg (line 15983): its proof cast only.
   tests/relcast_absent.expect checks the logs. *)
Register eq as lean.rel_transport.
Set Warnings "+unknown-option".
Set Lean Error Mode "Skip".
Set Lean Entry Timeout 10.
Redirect "relcast_absent_lib.log" Lean Import "../dumps/lean434/relcast.ndjson" 1 15434.
Redirect "relcast_absent_theorem.log" Lean Import "../dumps/lean434/relcast.ndjson" 15434 15435.
Redirect "relcast_absent_h_pair.log" Lean Import "../dumps/lean434/relcast.ndjson" 15818 15825.
Redirect "relcast_absent_rel_arg.log" Lean Import "../dumps/lean434/relcast.ndjson" 15948 15984.
Check RLI434RC_rel_arg.
