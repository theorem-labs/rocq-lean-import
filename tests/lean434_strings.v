From LeanImport Require Import Lean.

(* A string literal of a Lean v4.34.0 export (RLI434.astral := "Ax", export line 343136): the new path writes
   it as String.ofList over Char.ofNat, and Char.ofNatAux, behind Char.ofNat, imports by the transport of its
   proof argument. The import runs in Skip mode, because entries before it that this work does not fix (a
   Nat.Linear reflection proof, Nat.mul_add_div._f, and what stands behind it) are refused; they are
   tests/lean434_string_length.v. *)
Set Lean Error Mode "Skip".
Set Warnings "+unknown-option".
Set Lean Entry Timeout 5.
Redirect "lean434_strings.log" Lean Import "../dumps/lean434/strings.ndjson".

Check RLI434_astral.
