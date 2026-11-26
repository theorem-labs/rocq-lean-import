From LeanImport Require Import Lean.

(* A Fin lemma the kernel refuses (README, "Transport of proof arguments across Nat literals"): the pass logs it,
   uses no lemma, and leaves the argument as it is. dumps/lean434/fin_lemma_refused.ndjson is dumps/lean434/shape.ndjson
   up to RLI434S.cast_127 with the library's Nat.mod renamed Nat.modLib, a new constant Nat.mod := fun x y => 0, and
     RLI434S.lemma_refused : forall v : UInt32, v <= UInt32.ofNatLT 127 _ ->
       v <= id (UInt32.ofBitVec (BitVec.ofFin 32 (Fin.mk (2 ^ 32) (Nat.mod 127 (2 ^ 32)) _)))
   (export line 8554; its row in dumps/lean434/README.md). The pass reads Nat.mod by its name and finds both Fin values
   127, so it generates RLI434S_lemma_refused__nat_eq_1 : 127 = Nat.mod 127 (2 ^ 32), which the kernel refuses (this
   Nat.mod is 0). No argument is cast, Lean's value goes to the kernel, which refuses the entry, and the lemma is not
   declared. The src/ of the fix's parent generates no Fin lemma and logs no refusal (ci/build-9.2-cut.sh --revert-fix).
   tests/fin_transport_lemma_refused.expect checks the log. *)
Set Warnings "+unknown-option".
Set Lean Error Mode "Skip".
Set Lean Entry Timeout 10.
Redirect "fin_transport_lemma_refused.log" Lean Import "../dumps/lean434/fin_lemma_refused.ndjson".

Fail Check RLI434S_lemma_refused__nat_eq_1.
Fail Check RLI434S_lemma_refused.
(* W21: optional diagnostic formatting must not stop the next declaration. *)
Check RLI434S_after_refusal.
