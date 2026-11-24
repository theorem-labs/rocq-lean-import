From LeanImport Require Import Lean.

(* Lean's proof that a valid code point is below UInt32.size (isValidChar_UInt32 and its match), checked
   against Lean's own Nat.isValidChar and UInt32.size on the new path: the entries of dumps/lean434/char.ndjson
   up to export line 5096 (the range 1 5097 reads it). Char.ofNatAux, after it, is tests/lean434_char.v. *)
Set Lean Error Mode "Fail".
Lean Import "../dumps/lean434/char.ndjson" 1 5097.

Check _private_Init_Prelude0_isValidChar_UInt32_match_1_1.
Check _private_Init_Prelude0_isValidChar_UInt32.
