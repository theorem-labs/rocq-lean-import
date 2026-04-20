From LeanImport Require Import Lean.

(* The dump declares [UInt32] twice (Fin shape then BitVec shape) and
   [Char] twice in the same positions; the second [#IND]s overwrite
   the first bindings.  "Skip" tolerates the non-idempotent recursor
   redeclaration; [add_declared] runs before the scheme step fails. *)

Set Lean Error Mode "Skip".
Lean Import "../dumps/uint32_dispatch".

Check make_uint32_legacy : Fin UInt32_size -> UInt32_legacy.
Check char_wrapper_legacy : Char_legacy -> Char_legacy.
Check make_uint32_bitvec : BitVec 32 -> UInt32.
Check char_wrapper_bitvec : Char -> Char.
