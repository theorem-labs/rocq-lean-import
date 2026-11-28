From LeanImport Require Import Lean.

(* Lean's _private.Init.Data.String.Decode.0.Char.toNat_le._proof_1_1, the last entry of
   dumps/lean434/tonat_le.ndjson (export line 75794), which is exported from that theorem alone. The importer
   appends a numeric name component to the one before it, so the log names it
   _private.Init.Data.String.Decode0.Char.toNat_le._proof_1_1. Every entry before it imports at an 8 MiB soft
   stack; this one does not: its import ends in Stack overflow. at a soft stack of 8, 16, 32 and 64 MiB, and
   completes at 128 MiB. ci/build-9.2-cut.sh --revert-fix uses the head's src/ on both sides. The head side
   passes at CUT_STACK_KIB=131072. The parent side keeps the default soft stack (8 MiB on Linux unless raised),
   because the parent of the stack fix has no CUT_STACK_KIB line. At 8 MiB the import refuses this entry first. *)
Set Lean Error Mode "Fail".
Redirect "lean434_stack.log" Lean Import "../dumps/lean434/tonat_le.ndjson".

Check _private_Init_Data_String_Decode0_Char_toNat_le__proof_1_1.
