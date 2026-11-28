From LeanImport Require Import Lean.

(* Char.ofNatAux (export line 5118) and Char.ofNat, Lean's own, with the matcher of the proof
   _private.Init.Prelude.0.isValidChar_UInt32 they need (tests/lean434_isvalidchar.v is that proof alone).
   The inventory row names two entries. A Char is a structure over UInt32, a structure over BitVec 32, and the
   value of Char.ofNatAux is built with BitVec.ofNatLT, so no export of Char.ofNatAux leaves out BitVec and
   BitVec.ofNatLT (export line 1224), which comes first: the base source, without the fix 50081965, refuses
   BitVec.ofNatLT (missing BitVec.ofFin) before it reaches Char.ofNatAux. The src/ of 69c45616, the parent of
   the fix 17ac70f1 (ci/build-9.2-cut.sh --revert-fix), imports BitVec.ofNatLT and refuses Char.ofNatAux first
   (Stack overflow.). *)
Set Lean Error Mode "Fail".
Lean Import "../dumps/lean434/char.ndjson".

Check _private_Init_Prelude0_isValidChar_UInt32_match_1_1.
Check Char_ofNatAux.
Check Char_ofNat.
