From LeanImport Require Import Lean.

Set Lean Error Mode "Fail".
Lean Import "../dumps/lean434/bitvec_uint32.ndjson".

Check BitVec_ofFin.
Check BitVec_ofNatLT.
Check UInt32_ofBitVec : BitVec 32 -> UInt32.
Check UInt32_toBitVec : UInt32 -> BitVec 32.
Check UInt32_add : UInt32 -> UInt32 -> UInt32.

(* Exercise each export name through its declared type. *)
Check (fun (b : BitVec 32) => UInt32_toBitVec (UInt32_ofBitVec b)).
