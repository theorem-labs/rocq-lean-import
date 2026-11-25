From LeanImport Require Import Lean.

(* A string literal of a Lean v4.34.0 export (RLI434.astral := "𝔸x", export line 343136): the new path writes
   it as String.ofList over Char.ofNat, and Char.ofNatAux, behind Char.ofNat, imports by the transport of its
   proof argument. The import runs in Skip mode, because entries before it that this work does not fix (a
   Nat.Linear reflection proof, Nat.mul_add_div._f, and what stands behind it) are refused; they are
   tests/lean434_string_length.v. The slowest entry RLI434.astral needs is
   _private.Init.Prelude.0.isValidChar_UInt32 (export line 54541). It took 9.2 s and 11.7 s in two trials
   on the Rocq 9.2 cut at an 8 MiB stack, and more than 5 s in another trial.
   The 30 s limit is more than twice the longest of the two completed measurements quoted here. *)
Set Lean Error Mode "Skip".
Set Warnings "+unknown-option".
Set Lean Entry Timeout 30.
Redirect "lean434_strings.log" Lean Import "../dumps/lean434/strings.ndjson".

Check RLI434_astral.
