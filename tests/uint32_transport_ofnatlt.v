From LeanImport Require Import Lean.

(* UInt32.ofNatLT n h := ⟨BitVec.ofNatLT n h⟩ passes a proof of n < UInt32.size where BitVec.ofNatLT expects
   n < 2 ^ 32, and the transport of SProp arguments across Nat literals (README, "Transport of proof arguments
   across Nat literals") casts it along a generated lemma, UInt32.size = 2 ^ 32. dumps/lean434/uint32_ofnatlt.ndjson
   is exported from UInt32.ofNatLT and UInt32.toNat_ofNatLT alone and is imported alone, so the lemma is
   UInt32.ofNatLT's own (tests/nat_transport.v imports UInt32.ofNatLT after Char.ofNatAux, whose lemma it reuses).
   tests/uint32_transport_ofnatlt.expect checks the log. The inventory row names two entries: the base source
   refuses BitVec.ofNatLT (export line 1048) first, before UInt32.ofNatLT (export line 1062); the src/ of
   69c45616, the parent of the fix 17ac70f1 (ci/build-9.2-cut.sh --revert-fix), imports BitVec.ofNatLT and
   refuses UInt32.ofNatLT first (Stack overflow.). *)
Set Lean Error Mode "Fail".
Redirect "uint32_transport_ofnatlt.log" Lean Import "../dumps/lean434/uint32_ofnatlt.ndjson".

Check UInt32_ofNatLT.
Check UInt32_toNat_ofNatLT.
Check UInt32_ofNatLT__nat_eq_1.
(* The data of UInt32.ofNatLT is Lean's: its toNat is n by conversion. *)
Check (fun (n : Nat) h => eq_refl n : eq (UInt32_toNat (UInt32_ofNatLT n h)) n).
