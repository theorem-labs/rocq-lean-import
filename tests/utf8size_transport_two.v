From LeanImport Require Import Lean.

(* Lean 4.34.0's Char.utf8Size_eq_two_iff (Init/Data/String/Decode.lean 36-41) states 127 < c.val /\ c.val <= 0x7ff
   and passes proofs at the thresholds UInt32.ofNatLT 127 _ and UInt32.ofNatLT 2047 _, two Fin holes in some of its
   arguments, each cast along its own lemma (README, "Transport of proof arguments across Nat literals"). Its
   transport pass needs 1,454,640 steps in all: 435,000 for its own scans and walks and 1,019,640 for the 128
   arguments it looks at, the largest of which needs 35,933. Each of these parts has the step budget, 1,000,000 by
   default, and the entry as a whole ten times that (README, "Lean Transport Step Budget"), so the pass completes.
   dumps/lean434/utf8size_two.ndjson is exported from Char.utf8Size_eq_two_iff alone (export line 11778). The src/
   of the fix's parent stops the pass at 1,000,000 steps for the whole entry and refuses the entry at the 120 s
   limit below (ci/build-9.2-cut.sh --revert-fix). tests/utf8size_transport_two.expect checks the log. *)
Set Warnings "+unknown-option".
Set Lean Entry Timeout 120.
Set Lean Error Mode "Fail".
Redirect "utf8size_transport_two.log" Lean Import "../dumps/lean434/utf8size_two.ndjson".

Check Char_utf8Size_eq_two_iff.
Check Char_utf8Size_eq_two_iff__nat_eq_1.
Check Char_utf8Size_eq_two_iff__nat_eq_2.
Check Char_utf8Size_eq_two_iff__nat_eq_3.
