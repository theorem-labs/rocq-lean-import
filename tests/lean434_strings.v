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
(* The inventory row names two entries. A Lean 4.34 String holds a ByteArray of UInt8, whose closure holds
   BitVec, so the literal cannot be the first entry refused: without the fix 50081965 the first is
   Nat.pow_pos._f (export line 9131). The row's own entry, RLI434.astral, is decided by the r5 line below
   (ci/build-9.2-cut.sh --revert-fix): on the src/ of c6c1c9d4, the parent of 50081965, the import skips
   RLI434.astral with "missing String" (it refused the String entry, export line 9552, with "missing
   ByteArray.IsValidUTF8"), and tests/lean434_strings.expect refuses that line after the compile: *)
(* r5 assertion: "lean434_strings.log" Skipping: Error at line 343136 (for RLI434.astral) *)
Redirect "lean434_strings.log" Lean Import "../dumps/lean434/strings.ndjson".

(* RLI434.astral is declared: tests/lean434_strings.expect reads this log. Locate does not fail when no constant
   has the name, so the compile ends normally and the .expect is checked also when the import skipped it. *)
Redirect "lean434_strings_locate.log" Locate RLI434_astral.
