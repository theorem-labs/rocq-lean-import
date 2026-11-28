From LeanImport Require Import Lean.

(* F6: Lean's proof that a valid code point is below UInt32.size (_private.Init.Prelude.0.isValidChar_UInt32)
   and its matcher, checked against Lean's own Nat.isValidChar and UInt32.size on the new path.
   dumps/lean434/isvalidchar.ndjson is exported from that theorem alone. Its closure has no BitVec, no UInt32
   type and no Char entry (UInt32.size, the Nat 4294967296, is its only UInt32 name), so without the fix
   50081965 at 8192 KiB the first entry refused is the matcher (export line 563, Stack overflow.), on the
   base source as on the src/ of the fix's parent c6c1c9d4. ci/build-9.2-cut.sh --revert-fix runs both sides
   at 8192 KiB: at the readings' 131072 KiB the stack alone lets the parent's src/ import the matcher, so the
   reading counts that entry under the stack, not the source fix. The importer appends a numeric name
   component to the one before it, so the log names it _private.Init.Prelude0.isValidChar_UInt32.match_1_1.
   Char.ofNatAux, which needs this theorem, is tests/lean434_char.v. *)
Set Lean Error Mode "Fail".
Lean Import "../dumps/lean434/isvalidchar.ndjson".

Check _private_Init_Prelude0_isValidChar_UInt32_match_1_1.
Check _private_Init_Prelude0_isValidChar_UInt32.
