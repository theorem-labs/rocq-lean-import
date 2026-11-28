From LeanImport Require Import Lean.

(* UInt32.toNat_shiftLeft, Lean's theorem (a <<< b).toNat = a.toNat <<< (b.toNat % 32) % 2 ^ 32, proved by simp
   over the BitVec lemmas: the transport of SProp arguments across Nat literals (README, "Transport of proof
   arguments across Nat literals") casts two arguments of its proof, along two generated lemmas between 2 ^ 32
   and a Nat literal, one in each direction (the Check lines below print them).
   dumps/lean434/uint32_shiftleft.ndjson is exported from UInt32.toNat_shiftLeft alone. Its closure does not hold
   UInt32.ofNatLT (tests/uint32_transport_ofnatlt.v), so the import runs in Fail mode and its first refusal is
   the verdict. tests/uint32_transport_shiftleft.expect checks the log. The inventory row names two entries: the
   base source refuses Nat.pow_pos._f (export line 8118) first; the src/ of 69c45616, the parent of the fix
   17ac70f1 (ci/build-9.2-cut.sh --revert-fix), refuses UInt32.toNat_shiftLeft (export line 12253) first
   (Stack overflow.). *)
Set Lean Error Mode "Fail".
Redirect "uint32_transport_shiftleft.log" Lean Import "../dumps/lean434/uint32_shiftleft.ndjson".

Check UInt32_toNat_shiftLeft.
Check UInt32_toNat_shiftLeft__nat_eq_1.
Check UInt32_toNat_shiftLeft__nat_eq_2.
